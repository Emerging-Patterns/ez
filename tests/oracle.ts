#!/usr/bin/env bun
// A local stand-in for the hub, so `bend --publish` can be run without touching
// hub.bend-lang.com. It accepts the POST, computes the package hash the way
// cli_publish does, writes the package out, and answers with that hash (which
// is what bend checks the response against).
//   bun tests/oracle.ts <dir> <port>
import { mkdirSync, writeFileSync } from "node:fs";
import * as path from "node:path";

const dir = process.argv[2];
const port = Number(process.argv[3]);

function sha256(text: string): string {
  return new Bun.CryptoHasher("sha256").update(text).digest("hex");
}

Bun.serve({
  port,
  hostname: "127.0.0.1",
  async fetch(req) {
    if (req.method !== "POST") {
      const at = path.join(dir, new URL(req.url).pathname);
      const f = Bun.file(at);
      return await f.exists() ? new Response(f) : new Response("", { status: 404 });
    }
    const { files } = await req.json() as { files: Record<string, string> };
    const paths = Object.keys(files).sort();
    const manifest = paths.map((p) => sha256(files[p]) + " " + p + "\n").join("");
    const hash = "0x" + sha256(manifest).slice(0, 32);
    for (const p of paths) {
      const at = path.join(dir, hash, p);
      mkdirSync(path.dirname(at), { recursive: true });
      writeFileSync(at, files[p]);
    }
    writeFileSync(path.join(dir, hash, "manifest"), manifest);
    writeFileSync(path.join(dir, hash + ".files.json"), JSON.stringify(files, null, 2));
    return new Response(hash);
  },
});
