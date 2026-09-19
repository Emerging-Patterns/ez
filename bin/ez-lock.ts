#!/usr/bin/env bun
// ez lock: walk a .bend entry's import graph, resolve every `0x<hash>/<path>`
// hub import transitively, and write ez.lock.json. Nix reads that file and
// fetches each entry as a fixed-output derivation, so `bend` never touches the
// network inside the sandbox.
import { existsSync, readFileSync } from "node:fs";
import * as path from "node:path";

const HUB = process.env.BEND_HUB ?? "https://hub.bend-lang.com";

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
    break; // imports head the file; the first other statement ends them
  }
  return out;
}

// bend accepts any prefix of the sha256 as the hash; hub paths use the full dir
function hub_get(sub: string, want: string): Promise<string> {
  return fetch(HUB + "/" + sub).then(async (res) => {
    const src = res.ok ? await res.text() : "";
    const sum = new Bun.CryptoHasher("sha256").update(src).digest("hex");
    if (!res.ok || want.length < 32 || sum.slice(0, want.length) !== want) {
      throw new Error(HUB + "/" + sub + " does not hash to " + want);
    }
    return src;
  });
}

type Pkg = { manifest: string; files: Record<string, string> };

// one hub package: its manifest, every file, and their sha256s
async function pkg_read(hash: string): Promise<Pkg> {
  const manifest = await hub_get(hash + "/manifest", hash.slice(2));
  const rows = manifest.trim().split("\n").map((l) => l.split(" "));
  const files: Record<string, string> = {};
  for (const [sum, at] of rows) {
    if (path.posix.normalize("/" + at) !== "/" + at) {
      throw new Error(hash + ": manifest escapes the package (" + at + ")");
    }
    files[at] = sum;
  }
  await Promise.all(rows.map(([sum, at]) => hub_get(hash + "/" + at, sum)));
  return { manifest, files };
}

// the hashes a package's own sources import, so the walk reaches grandchildren
async function pkg_deps(hash: string, files: Record<string, string>): Promise<string[]> {
  const out: string[] = [];
  for (const at of Object.keys(files)) {
    const src = await hub_get(hash + "/" + at, files[at]);
    for (const spec of imports(src)) {
      const m = /^(0x[0-9a-f]+)\//.exec(spec);
      if (m !== null) out.push(m[1]);
    }
  }
  return out;
}

// local files import local files; follow those too, so a multi-file project
// locks the hub packages any of its modules reach
function roots(entry: string, seen: Set<string>): string[] {
  const real = path.resolve(entry);
  if (seen.has(real) || !existsSync(real)) return [];
  seen.add(real);
  const out: string[] = [];
  const dir = path.dirname(real);
  for (const spec of imports(readFileSync(real, "utf8"))) {
    const m = /^(0x[0-9a-f]+)\//.exec(spec);
    if (m !== null) {
      out.push(m[1]);
      continue;
    }
    out.push(...roots(path.join(dir, spec), seen));
  }
  return out;
}

async function main() {
  const entry = process.argv[2];
  if (entry === undefined) {
    process.stderr.write("usage: ez-lock <entry.bend>\n");
    process.exit(1);
  }
  const queue = roots(entry, new Set());
  const pkgs: Record<string, Pkg> = {};
  while (queue.length > 0) {
    const hash = queue.shift()!;
    if (pkgs[hash] !== undefined) continue;
    const pkg = await pkg_read(hash);
    pkgs[hash] = pkg;
    queue.push(...await pkg_deps(hash, pkg.files));
  }
  const lock = {
    schemaVersion: 1,
    hub: HUB,
    bend: (Bun.spawnSync(["bend", "--version"]).stdout.toString().trim().split(" ")[1]) ?? "unknown",
    packages: Object.fromEntries(
      Object.keys(pkgs).sort().map((h) => [h, pkgs[h].files]),
    ),
  };
  process.stdout.write(JSON.stringify(lock, null, 2) + "\n");
}

await main();
