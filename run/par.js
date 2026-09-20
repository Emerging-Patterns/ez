// ezrun.par: the JS lane's twin of par.c. The fields arrive the way par.c
// takes them and go straight to spawnSync, so no shell parses them.
//
// This one runs the jobs in turn rather than at once. Bend's JS effects answer
// synchronously, and node has no way to wait on several spawned children from
// inside a synchronous call, so the lane that could run them together is the
// one that cannot say when they are done. The answer is the same either way —
// every status, in the order the jobs were given — and ez ships as a native
// binary, which is what the gate actually runs.
function ezrun_par(cmd) {
  const cp = require("child_process");
  const fs = require("fs");
  const line = cmd.split("\n");
  const dir = line.length > 2 ? line[2] : ".";
  const by = line.length > 3 ? parseInt(line[3], 10) : 0;
  const codes = [];
  let i = 4;
  let n = 0;
  while (i < line.length) {
    const argc = parseInt(line[i], 10);
    if (!(argc > 0)) {
      break;
    }
    const args = line.slice(i + 1, i + 1 + argc);
    i += argc + 1;
    const spare = by > 0 ? by - Math.floor(Date.now() / 1000) : 0;
    if (by > 0 && spare <= 0) {
      codes.push(124);
      n += 1;
      continue;
    }
    const out = fs.openSync(dir + "/" + n, "w");
    try {
      const r = cp.spawnSync(args[0], args.slice(1),
        { stdio: ["ignore", out, out], timeout: by > 0 ? spare * 1000 : undefined });
      codes.push(r.error !== undefined && r.error !== null ? 127 : r.status === null ? 124 : r.status);
    } catch (e) {
      codes.push(127);
    }
    fs.closeSync(out);
    n += 1;
  }
  return codes.join("\n");
}
