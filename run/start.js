// ezrun.start: the JS lane's twin of start.c. The arguments arrive newline
// separated and go straight to spawn, so no shell parses them. The child is
// detached and its streams are dropped, so this process can exit while it runs
// and nothing it prints can be mistaken for an answer.
function ezrun_start(cmd) {
  const cp = require("child_process");
  const args = cmd.split("\n");
  try {
    const child = cp.spawn(args[0], args.slice(1), { detached: true, stdio: "ignore" });
    child.unref();
    return String(child.pid ?? 0);
  } catch (e) {
    return "0";
  }
}
