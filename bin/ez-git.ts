#!/usr/bin/env bun
// ez git: depend on a Bend project that was never published to the hub.
//
// Clones the repo at a pinned rev, computes the `0x<hash>` that
// `bend <entry> --publish` would have produced for it, and writes the package
// into the local BEND_LIB under that name. The import line you get is the same
// one a published package would give you, so if upstream publishes later the
// hash is unchanged and the hub simply starts serving it.
//
//   bun bin/ez-git.ts https://github.com/owner/repo <rev> src/lib.bend
import { mkdirSync, readFileSync, writeFileSync, existsSync, rmSync, cpSync } from "node:fs";
import * as path from "node:path";
import { pkg_of, manifest_of } from "./pkg.ts";

const LIB = path.resolve(process.env.BEND_LIB ?? ".ez/lib");
const ORIGINS = path.join(path.dirname(LIB), "origins.toml");

// the origins already written down. The file is ez's own TOML subset: a
// `[origins."<hash>"]` table per package, holding only string values.
function read_origins(): Record<string, Record<string, string>> {
  if (!existsSync(ORIGINS)) return {};
  const out: Record<string, Record<string, string>> = {};
  let at: Record<string, string> | null = null;
  for (const raw of readFileSync(ORIGINS, "utf8").split("\n")) {
    const line = raw.trim();
    const head = /^\[origins\."([^"]+)"\]$/.exec(line);
    if (head !== null) {
      at = {};
      out[head[1]] = at;
      continue;
    }
    const kv = /^([A-Za-z0-9_-]+) = "(.*)"$/.exec(line);
    if (kv !== null && at !== null) at[kv[1]] = kv[2];
  }
  return out;
}

function write_origins(origins: Record<string, Record<string, string>>): void {
  const text = Object.keys(origins).sort().map((h) =>
    "[origins." + JSON.stringify(h) + "]\n" +
    Object.entries(origins[h]).map(([k, v]) => k + " = " + JSON.stringify(v) + "\n").join("")
  ).join("\n");
  mkdirSync(path.dirname(ORIGINS), { recursive: true });
  writeFileSync(ORIGINS, text);
}

function git(...args: string[]): void {
  const r = Bun.spawnSync(["git", ...args], { stdout: "ignore", stderr: "pipe" });
  if (r.exitCode !== 0) throw new Error("git " + args.join(" ") + ": " + r.stderr.toString().trim());
}

// a tag or branch is what a human asks for; the commit it names is what gets
// pinned, and both are written down so an upgrade knows what to re-resolve
function resolve(url: string, ref: string): { rev: string; tag?: string } {
  if (/^[0-9a-f]{40}$/.test(ref)) return { rev: ref };
  const r = Bun.spawnSync(["git", "ls-remote", url, ref, "refs/tags/" + ref + "^{}"]);
  if (r.exitCode !== 0) throw new Error("git ls-remote " + url + ": " + r.stderr.toString().trim());
  const rows = r.stdout.toString().trim().split("\n").filter((l) => l !== "")
    .map((l) => l.split("\t"));
  if (rows.length === 0) throw new Error(url + " has no ref named " + ref);
  // an annotated tag resolves through its peeled ^{} row, which is the commit
  const peeled = rows.find(([, at]) => at.endsWith("^{}"));
  return { rev: (peeled ?? rows[0])[0], tag: ref };
}

function main() {
  const [url, ref, entry] = process.argv.slice(2);
  if (entry === undefined) {
    process.stderr.write("usage: ez-git <url> <rev|tag|branch> <entry.bend>\n");
    process.exit(1);
  }
  const { rev, tag } = resolve(url, ref);

  const work = path.join(LIB, ".work-" + rev);
  rmSync(work, { recursive: true, force: true });
  mkdirSync(work, { recursive: true });
  git("init", "-q", work);
  git("-C", work, "fetch", "-q", "--depth", "1", url, rev);
  git("-C", work, "checkout", "-q", rev);

  // fetchgit's hash is the NAR of the checkout without .git, so take it here
  rmSync(path.join(work, ".git"), { recursive: true, force: true });
  const nar = Bun.spawnSync(["nix", "hash", "path", "--type", "sha256", "--sri", work]);
  if (nar.exitCode !== 0) throw new Error("nix hash path: " + nar.stderr.toString().trim());
  const narHash = nar.stdout.toString().trim();

  const at = path.join(work, entry);
  if (!existsSync(at)) throw new Error(entry + " is not in " + url + " at " + rev);
  const pkg = pkg_of(at);

  // lay the package out the way the hub serves it, so bend finds it with no fetch
  const dst = path.join(LIB, pkg.hash);
  rmSync(dst, { recursive: true, force: true });
  // a package's paths are written from its root, which is the entry's own
  // directory only when no module of it was reached through `..`
  const from = pkg.root;
  for (const p of Object.keys(pkg.files)) {
    mkdirSync(path.join(dst, path.dirname(p)), { recursive: true });
    cpSync(path.join(from, p), path.join(dst, p));
  }
  writeFileSync(path.join(dst, "manifest"), manifest_of(pkg.files));
  rmSync(work, { recursive: true, force: true });

  const origins = read_origins();
  origins[pkg.hash] = {
    kind: "git", url, rev, entry, root: path.relative(work, pkg.root) || ".", narHash,
    ...(tag === undefined ? {} : { tag }),
  };
  write_origins(origins);

  // stdout is the record, five lines, for whatever writes the ledger; anything
  // a person reads goes to stderr
  const name = path.basename(entry, ".bend");
  process.stdout.write([pkg.hash, url, rev, tag ?? "", entry].join("\n") + "\n");
  if (tag !== undefined) process.stderr.write(tag + " is " + rev + "\n");
  process.stderr.write("import " + pkg.hash + "/" + path.basename(entry) + " as " +
    name[0].toUpperCase() + name.slice(1) + "\n");
}

main();
