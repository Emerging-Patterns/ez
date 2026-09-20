// ezrun.start: starts a program and leaves it running, answering with its pid.
//
// The arguments arrive the way exec.c takes them, one string with newlines
// between, and go to execvp as a vector, so no shell sees them. The difference
// is what happens next: nothing is waited for and nothing is read. The child
// gets a session of its own and /dev/null for all three of its streams, so it
// never holds open a pipe someone is reading to the end.
#include <fcntl.h>
#include <unistd.h>

Term ezrun_start_run(Env e, Term* f, IoWork* w) {
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

  pid_t pid = fork();
  if (pid == 0) {
    setsid();
    int nul = open("/dev/null", O_RDWR);
    dup2(nul, 0);
    dup2(nul, 1);
    dup2(nul, 2);
    if (nul > 2) {
      close(nul);
    }
    execvp(argv[0], argv);
    _exit(127);
  }

  char out[16];
  int on = snprintf(out, sizeof(out), "%d", pid > 0 ? (int)pid : 0);

  free(argv);
  free(cmd);
  return io_str(e, out, (size_t)on);
}

static void __attribute__((constructor)) ezrun_start_use(void) {
  io_eff(CID_EZRUN_START, ezrun_start_run, 0);
}
