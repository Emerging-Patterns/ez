// ezpass.run: the JS lane's twin of pass.c. The arguments arrive newline
// separated and go straight to spawnSync on this process's own stdio, so no
// shell parses them and nothing is captured.
function ezpass_run(cmd) {
  const cp = require("child_process");
  const args = cmd.split("\n");
  const r = cp.spawnSync(args[0], args.slice(1), { stdio: "inherit" });
  if (r.error !== undefined && r.error !== null) {
    return 127;
  }
  if (r.status === null) {
    return 128 + (require("os").constants.signals[r.signal] ?? 0);
  }
  return r.status;
}
