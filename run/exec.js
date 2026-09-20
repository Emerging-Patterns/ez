// ezrun.exec: the JS lane's twin of exec.c. The arguments arrive newline
// separated and go straight to spawnSync, so no shell parses them.
function ezrun_exec(cmd) {
  const cp = require("child_process");
  const args = cmd.split("\n");
  const r = cp.spawnSync(args[0], args.slice(1), { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
  const code = r.error !== undefined && r.error !== null ? 127 : r.status === null ? 128 : r.status;
  return String(code) + "\n" + (r.stdout ?? "") + (r.stderr ?? "");
}
