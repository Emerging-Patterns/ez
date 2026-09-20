// The package a `bend <entry> --publish` would upload, computed without
// publishing: the file set, their sha256s, and the `0x<hash>` that names them.
//
// This mirrors `pkg_files` and the hash in bend's `cli_publish`. tests/publish.sh
// pins it against the real thing by running `bend --publish` at a local hub and
// comparing the two hashes, so drift fails the gate rather than the ecosystem.
import { existsSync, readFileSync, realpathSync } from "node:fs";
import * as path from "node:path";

export type Pkg = { hash: string; root: string; files: Record<string, string> };

export function sha256(text: string): string {
  return new Bun.CryptoHasher("sha256").update(text).digest("hex");
}

// every `import <spec> as <Name>` in the header, plus the foreign `import "x.c"`
// bodies, which bend uploads alongside the .bend sources
function scan(src: string): { mods: string[]; foreign: string[] } {
  const mods: string[] = [];
  const foreign: string[] = [];
  let head = true;
  for (const raw of src.split("\n")) {
    const line = raw.trim();
    const f = /^import\s+"([^"]+)"\s*$/.exec(line);
    if (f !== null) {
      foreign.push(f[1]);
      continue;
    }
    if (!head) continue;
    if (line === "" || line.startsWith("#")) continue;
    const m = /^import\s+(\S+)\s+as\s+[A-Za-z_][A-Za-z0-9_]*\s*(?:#.*)?$/.exec(line);
    if (m !== null) {
      mods.push(m[1]);
      continue;
    }
    if (/^import\s+Base\s*$/.test(line)) continue;
    head = false; // the imports head the file; the first other statement ends them
  }
  return { mods, foreign };
}

// bend names a module by the path it was reached through, with .bend stripped;
// the entry is "", and an `import 0x...` is a hub package, not part of this one
function walk(
  file: string,
  ns: string,
  seen: Map<string, string>,
  out: { raw: string; real: string }[],
  entry: string,
): void {
  const real = realpathSync(file);
  if (seen.has(real)) return;
  seen.set(real, ns);
  const src = readFileSync(real, "utf8");
  const { mods, foreign } = scan(src);
  out.push({ raw: ns === "" ? path.basename(entry) : ns + ".bend", real });
  // a foreign body is named the way its importing module is, from that module's
  // own directory: `bend --publish` writes src/util/beep.c for a body imported
  // by src/util/math.bend
  for (const at of foreign) {
    const to = path.resolve(path.dirname(real), at);
    if (existsSync(to)) out.push({ raw: path.posix.join(path.posix.dirname(ns), at), real: to });
  }
  for (const rel of mods) {
    if (/^0x[0-9a-f]+\//.test(rel)) continue;
    const next = path.posix.normalize(rel);
    walk(path.join(path.dirname(real), next), path.posix.join(path.posix.dirname(ns), next).replace(/\.bend$/, ""), seen, out, entry);
  }
}

export function pkg_of(entry: string): Pkg {
  const raws: { raw: string; real: string }[] = [];
  walk(entry, "", new Map(), raws, entry);
  // a module reached through `..` re-roots the package under that many trailing
  // components of the entry's own directory, so no path escapes the package
  const ups = raws.map((r) => r.raw.split("/").filter((s) => s === "..").length);
  const up = Math.max(0, ...ups);
  const anc = realpathSync(path.dirname(entry)).split("/").slice(-up || Infinity);
  // the directory the file keys are written from, which is the entry's own only
  // when nothing climbed above it
  const root = path.posix.join(path.dirname(entry), ...Array(up).fill(".."));
  const files: Record<string, string> = {};
  for (const { raw, real } of raws) {
    const at = path.posix.join(...anc, raw);
    if (at.startsWith("/") || at.startsWith("..")) {
      throw new Error(real + " escapes the package (an absolute import, or a climb above the file system)");
    }
    files[at] = sha256(readFileSync(real, "utf8"));
  }
  return { hash: hash_of(files), root, files };
}

// the manifest text is the package's identity; bend checks a fetched manifest
// against the first 32 hex characters of its sha256
export function manifest_of(files: Record<string, string>): string {
  return Object.keys(files).sort().map((p) => files[p] + " " + p + "\n").join("");
}

export function hash_of(files: Record<string, string>): string {
  return "0x" + sha256(manifest_of(files)).slice(0, 32);
}
