// ezpass.run: runs a program with its arguments on this process's own stdin,
// stdout and stderr, waits for it, and answers the status it exited with.
//
// The arguments arrive in one string, newline separated, and are handed to
// execvp as a vector, so no shell sees them. Nothing is captured: what the
// program prints reaches the terminal as it prints it, and it reads what this
// process would have read. A program killed by a signal answers 128 plus the
// signal, as a shell reports it, and one that could not be started, 127.
#include <sys/wait.h>
#include <unistd.h>

Term ezpass_run_run(Env e, Term* f, IoWork* w) {
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

  // what this process printed so far goes out before the program's first line
  fflush(NULL);
  int code = 127;
  pid_t pid = fork();
  if (pid == 0) {
    execvp(argv[0], argv);
    _exit(127);
  }
  if (pid > 0) {
    int status = 0;
    pid_t got = waitpid(pid, &status, 0);
    while (got < 0 && errno == EINTR) {
      got = waitpid(pid, &status, 0);
    }
    if (got == pid) {
      code = WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
    }
  }

  free(argv);
  free(cmd);
  return (Term)(uint32_t)code;
}

static void __attribute__((constructor)) ezpass_run_use(void) {
  io_eff(CID_EZPASS_RUN, ezpass_run_run, 0);
}
