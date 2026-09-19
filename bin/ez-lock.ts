#!/usr/bin/env bun
// ez lock: walk a .bend entry's import graph, resolve every `0x<hash>` package
// transitively, and write ez.lock.json. Nix reads that file and fetches each
// package as a fixed-output derivation, so `bend` never touches the network
// inside the sandbox.
//
// A package resolves from the hub, or, when bin/ez-git.ts vendored it, from the
// git rev recorded in .ez/origins.json. Both end up as the same BEND_LIB tree.
import { existsSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { sha256 } from "./pkg.ts";

const HUB = process.env.BEND_HUB ?? "https://hub.bend-lang.com";
const LIB = path.resolve(process.env.BEND_LIB ?? ".ez/lib");
const ORIGINS = path.join(path.dirname(LIB), "origins.json");

type Source = { kind: "hub" } | { kind: "git"; url: string; rev: string; entry: string };
type Entry = { source: Source; files: Record<string, string> };

// every `import <spec> as <Name>` line, in source order
function imports(src: string): string[] {
  const out: string[] = [];
  for (const raw of src.split("\n")) {
    const line = raw.trim();
    if (line === "" || line.startsWith("#")) continue;
    const m = /^import\s+(\S+)\s+as\s+[A-Za-z_][A-Za-z0-9_]*\s*(?:#.*)?$/.exec(line);
    if (m !== null) {
      out.push(m[1]);
      continue;
    }
    if (/^import\s+Base\s*$/.test(line)) continue;
    break; // the imports head the file; the first other statement ends them
  }
  return out;
}

// bend accepts any prefix of the sha256 as the hash; hub paths use the full name
async function hub_get(sub: string, want: string): Promise<string> {
  const res = await fetch(HUB + "/" + sub);
  const src = res.ok ? await res.text() : "";
  if (!res.ok || want.length < 32 || sha256(src).slice(0, want.length) !== want) {
    throw new Error(HUB + "/" + sub + " does not hash to " + want);
  }
  return src;
}

function files_of(manifest: string, hash: string): Record<string, string> {
  const out: Record<string, string> = {};
  for (const [sum, at] of manifest.trim().split("\n").map((l) => l.split(" "))) {
    if (path.posix.normalize("/" + at) !== "/" + at) {
      throw new Error(hash + ": its manifest escapes the package (" + at + ")");
    }
    out[at] = sum;
  }
  return out;
}

// a vendored package is already on disk under BEND_LIB; a hub one is fetched and
// checked. Either way we end with its file list and the text of each file.
async function read(hash: string, source: Source): Promise<{ files: Record<string, string>; srcs: string[] }> {
  if (source.kind === "git") {
    const at = path.join(LIB, hash);
    const files = files_of(readFileSync(path.join(at, "manifest"), "utf8"), hash);
    const srcs = Object.keys(files).map((p) => readFileSync(path.join(at, p), "utf8"));
    for (const [i, p] of Object.keys(files).entries()) {
      if (sha256(srcs[i]) !== files[p]) throw new Error(hash + "/" + p + " does not match its manifest");
    }
    return { files, srcs };
  }
  const files = files_of(await hub_get(hash + "/manifest", hash.slice(2)), hash);
  const srcs = await Promise.all(Object.keys(files).map((p) => hub_get(hash + "/" + p, files[p])));
  return { files, srcs };
}

function hashes(specs: string[]): string[] {
  return specs.flatMap((s) => {
    const m = /^(0x[0-9a-f]+)\//.exec(s);
    return m === null ? [] : [m[1]];
  });
}

// local files import local files; follow those too, so a multi-file project
// locks every hub package any of its modules reaches
function roots(entry: string, seen: Set<string>): string[] {
  const real = path.resolve(entry);
  if (seen.has(real) || !existsSync(real)) return [];
  seen.add(real);
  const specs = imports(readFileSync(real, "utf8"));
  const dir = path.dirname(real);
  return [
    ...hashes(specs),
    ...specs.filter((s) => !/^0x[0-9a-f]+\//.test(s)).flatMap((s) => roots(path.join(dir, s), seen)),
  ];
}

async function main() {
  const entries = process.argv.slice(2);
  if (entries.length === 0) {
    process.stderr.write("usage: ez-lock <entry.bend>..\n");
    process.exit(1);
  }
  const origins: Record<string, Source> = existsSync(ORIGINS)
    ? JSON.parse(readFileSync(ORIGINS, "utf8"))
    : {};

  // a repo has as many roots as it has entry points, and the lock covers them all
  const seen = new Set<string>();
  const queue = entries.flatMap((e) => roots(e, seen));
  const packages: Record<string, Entry> = {};
  while (queue.length > 0) {
    const hash = queue.shift()!;
    if (packages[hash] !== undefined) continue;
    const source: Source = origins[hash] ?? { kind: "hub" };
    const { files, srcs } = await read(hash, source);
    packages[hash] = { source, files };
    queue.push(...srcs.flatMap((s) => hashes(imports(s))));
  }

  const lock = {
    schemaVersion: 2,
    hub: HUB,
    bend: Bun.spawnSync(["bend", "--version"]).stdout.toString().trim().split(" ")[1] ?? "unknown",
    packages: Object.fromEntries(Object.keys(packages).sort().map((h) => [h, packages[h]])),
  };
  process.stdout.write(JSON.stringify(lock, null, 2) + "\n");
}

await main();
