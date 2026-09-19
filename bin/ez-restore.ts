#!/usr/bin/env bun
// ez restore: fill BEND_LIB from ez.lock.json, so a checkout builds without
// re-resolving anything. This is what `nix/bend-lib.nix` does inside a sandbox,
// done here for people who are not building through nix.
//
//   bun bin/ez-restore.ts [ez.lock.json]
import { mkdirSync, writeFileSync, existsSync, rmSync, cpSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { sha256 } from "./pkg.ts";

const LIB = path.resolve(process.env.BEND_LIB ?? ".ez/lib");

type Source = { kind: "hub" } | { kind: "git"; url: string; rev: string; entry: string };
type Lock = {
  hub: string;
  packages: Record<string, { source: Source; files: Record<string, string> }>;
};

function put(hash: string, at: string, text: string, want: string): void {
  if (sha256(text) !== want) throw new Error(hash + "/" + at + " does not match the lock");
  const dst = path.join(LIB, hash, at);
  mkdirSync(path.dirname(dst), { recursive: true });
  writeFileSync(dst, text);
}

function manifest(files: Record<string, string>): string {
  return Object.keys(files).sort().map((p) => files[p] + " " + p + "\n").join("");
}

async function hub(url: string, hash: string, files: Record<string, string>): Promise<void> {
  for (const at of Object.keys(files)) {
    const res = await fetch(url + "/" + hash + "/" + at);
    if (!res.ok) throw new Error(url + "/" + hash + "/" + at + ": " + res.status);
    put(hash, at, await res.text(), files[at]);
  }
}

function git(hash: string, source: Source & { kind: "git" }, files: Record<string, string>): void {
  const work = path.join(LIB, ".work-" + source.rev);
  rmSync(work, { recursive: true, force: true });
  mkdirSync(work, { recursive: true });
  for (const args of [["init", "-q", work],
                      ["-C", work, "fetch", "-q", "--depth", "1", source.url, source.rev],
                      ["-C", work, "checkout", "-q", source.rev]]) {
    const r = Bun.spawnSync(["git", ...args], { stdout: "ignore", stderr: "pipe" });
    if (r.exitCode !== 0) throw new Error("git " + args.join(" ") + ": " + r.stderr.toString().trim());
  }
  // a package's paths are relative to its entry file's directory, not the repo root
  const from = path.join(work, path.dirname(source.entry));
  for (const at of Object.keys(files)) put(hash, at, readFileSync(path.join(from, at), "utf8"), files[at]);
  rmSync(work, { recursive: true, force: true });
}

async function main() {
  const lock: Lock = JSON.parse(readFileSync(process.argv[2] ?? "ez.lock.json", "utf8"));
  for (const [hash, entry] of Object.entries(lock.packages)) {
    rmSync(path.join(LIB, hash), { recursive: true, force: true });
    if (entry.source.kind === "git") git(hash, entry.source, entry.files);
    else await hub(lock.hub, hash, entry.files);
    writeFileSync(path.join(LIB, hash, "manifest"), manifest(entry.files));
    process.stderr.write(hash + " " + entry.source.kind + "\n");
  }
}

await main();
