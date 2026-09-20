// ezrun.exec: runs a program with its arguments and answers the exit status on
// its own first line, then everything the program printed.
//
// The arguments arrive in one string, newline separated, and are handed to
// execvp as a vector. No shell sees them, so a url or a rev out of a lockfile
// cannot become shell syntax. The child gets /dev/null for stdin and one pipe
// for stdout and stderr, so it cannot touch this program's own stdio.
#include <fcntl.h>
#include <sys/wait.h>
#include <unistd.h>

Term ezrun_exec_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* cmd = io_cstr(e, f[0], &n);

  // the newlines become terminators, so each argument is its own C string
  size_t argc = 1;
  for (size_t i = 0; i < (size_t)n; i++) {
    if (cmd[i] == '\n') {
      cmd[i] = '\0';
      argc++;
    }
  }
  char** argv = malloc((argc + 1) * sizeof(char*));
  size_t at = 0;
  argv[at++] = cmd;
  for (size_t i = 0; i + 1 < (size_t)n; i++) {
    if (cmd[i] == '\0') {
      argv[at++] = cmd + i + 1;
    }
  }
  argv[at] = NULL;

  size_t len = 0;
  size_t cap = 4096;
  char* buf = malloc(cap);
  int code = 127;
  int fds[2];
  if (pipe(fds) == 0) {
    pid_t pid = fork();
    if (pid == 0) {
      int nul = open("/dev/null", O_RDONLY);
      dup2(nul, 0);
      dup2(fds[1], 1);
      dup2(fds[1], 2);
      close(fds[0]);
      close(fds[1]);
      execvp(argv[0], argv);
      _exit(127);
    }
    close(fds[1]);
    ssize_t got;
    while ((got = read(fds[0], buf + len, cap - len)) > 0) {
      len += (size_t)got;
      if (len == cap) {
        cap *= 2;
        buf = realloc(buf, cap);
      }
    }
    close(fds[0]);
    if (pid > 0) {
      int status = 0;
      waitpid(pid, &status, 0);
      code = WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
    }
  }

  char head[16];
  int hn = snprintf(head, sizeof(head), "%d\n", code);
  char* out = malloc((size_t)hn + len);
  memcpy(out, head, (size_t)hn);
  memcpy(out + (size_t)hn, buf, len);

  free(buf);
  free(argv);
  free(cmd);
  Term s = io_str(e, out, (size_t)hn + len);
  free(out);
  return s;
}

static void __attribute__((constructor)) ezrun_exec_use(void) {
  io_eff(CID_EZRUN_EXEC, ezrun_exec_run, 0);
}
