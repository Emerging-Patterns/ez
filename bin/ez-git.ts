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
const ORIGINS = path.join(path.dirname(LIB), "origins.json");

function git(...args: string[]): void {
  const r = Bun.spawnSync(["git", ...args], { stdout: "ignore", stderr: "pipe" });
  if (r.exitCode !== 0) throw new Error("git " + args.join(" ") + ": " + r.stderr.toString().trim());
}

function main() {
  const [url, rev, entry] = process.argv.slice(2);
  if (entry === undefined) {
    process.stderr.write("usage: ez-git <url> <rev> <entry.bend>\n");
    process.exit(1);
  }
  if (!/^[0-9a-f]{40}$/.test(rev)) {
    process.stderr.write("ez-git: rev must be a full 40-character commit hash, not a branch or tag\n");
    process.exit(1);
  }

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
  const from = path.dirname(at);
  for (const p of Object.keys(pkg.files)) {
    mkdirSync(path.join(dst, path.dirname(p)), { recursive: true });
    cpSync(path.join(from, p), path.join(dst, p));
  }
  writeFileSync(path.join(dst, "manifest"), manifest_of(pkg.files));
  rmSync(work, { recursive: true, force: true });

  const origins = existsSync(ORIGINS) ? JSON.parse(readFileSync(ORIGINS, "utf8")) : {};
  origins[pkg.hash] = { kind: "git", url, rev, entry, narHash };
  mkdirSync(path.dirname(ORIGINS), { recursive: true });
  writeFileSync(ORIGINS, JSON.stringify(origins, null, 2) + "\n");

  const name = path.basename(entry, ".bend");
  process.stdout.write(pkg.hash + "\n");
  process.stdout.write("import " + pkg.hash + "/" + path.basename(entry) + " as " +
    name[0].toUpperCase() + name.slice(1) + "\n");
}

main();
