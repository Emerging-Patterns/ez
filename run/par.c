// ezrun.par: several programs run at once, each answered with its exit status.
//
// The arguments arrive as one string, every field on its own line: how many
// may run at once, how many gigabytes each was given, the directory they write
// into, and then each job as its argument count followed by that many
// arguments. A count before a job is what lets an argument hold anything a
// line may hold, so nothing has to invent a separator the way a `\x1e` between
// records would. No shell sees any of it, which is the promise exec.c makes
// and this keeps.
//
// A child's output goes to `<at>/<n>` rather than down a pipe. One pipe a
// child would mean polling every one of them at once or deadlocking on
// whichever filled its buffer first, and a file is what the caller reads back
// anyway.
//
// A width of 0 means the caller has no opinion and this works one out. Cores
// are the obvious ceiling and the wrong one on their own: every one of these
// runs under a memory cap, so what the machine can hold divides the answer as
// surely as what it can compute. What it can hold is the memory going spare
// rather than the memory it has — the cap bounds what one job may take, so a
// width read off the total would happily start seven jobs entitled to more
// than the machine has left and leave the kernel to sort it out.
//
// Spare means MemAvailable, which is the kernel's own estimate of what a new
// job could get, page cache it would reclaim included. `sysinfo` has no field
// for it: its freeram plus bufferram left out the 14 GB in Cached here and
// answered 2 where the kernel answered 4, which is a gate running at half the
// width the machine could carry. sysinfo is still the fallback for a system
// with no /proc.
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/sysinfo.h>
#include <sys/wait.h>
#include <unistd.h>

// the gigabytes a new job could have, by the kernel's own reckoning, or 0 when
// this system does not say
static double ezrun_par_spare(void) {
  FILE* f = fopen("/proc/meminfo", "r");
  if (f) {
    char name[64];
    unsigned long kb = 0;
    while (fscanf(f, "%63s %lu kB\n", name, &kb) == 2) {
      if (strcmp(name, "MemAvailable:") == 0) {
        fclose(f);
        return (double)kb / (1024.0 * 1024.0);
      }
    }
    fclose(f);
  }
  struct sysinfo si;
  if (sysinfo(&si) == 0) {
    double unit = si.mem_unit ? (double)si.mem_unit : 1.0;
    return (((double)si.freeram + (double)si.bufferram) * unit) /
      (1024.0 * 1024.0 * 1024.0);
  }
  return 0.0;
}

// how many of these may run at once, when the caller did not say
static int ezrun_par_width(int cap_gb) {
  long cores = sysconf(_SC_NPROCESSORS_ONLN);
  int n = cores > 0 ? (int)cores : 1;
  double gb = ezrun_par_spare();
  if (cap_gb > 0 && gb > 0.0) {
    int fits = (int)(gb / (double)cap_gb);
    if (fits < n) {
      n = fits;
    }
  }
  return n < 1 ? 1 : n;
}

// the job a finished child belonged to, so its status lands in the right place
static int ezrun_par_slot(pid_t* pids, int n, pid_t pid) {
  for (int i = 0; i < n; i++) {
    if (pids[i] == pid) {
      return i;
    }
  }
  return -1;
}

Term ezrun_par_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* cmd = io_cstr(e, f[0], &n);

  // the newlines become terminators, so each field is its own C string
  size_t lines = 1;
  for (size_t i = 0; i < (size_t)n; i++) {
    if (cmd[i] == '\n') {
      cmd[i] = '\0';
      lines++;
    }
  }
  char** line = malloc(lines * sizeof(char*));
  size_t at = 0;
  line[at++] = cmd;
  for (size_t i = 0; i + 1 < (size_t)n; i++) {
    if (cmd[i] == '\0') {
      line[at++] = cmd + i + 1;
    }
  }

  int want = lines > 0 ? atoi(line[0]) : 0;
  int cap_gb = lines > 1 ? atoi(line[1]) : 0;
  const char* dir = lines > 2 ? line[2] : ".";
  int width = want > 0 ? want : ezrun_par_width(cap_gb);

  // the jobs, each a vector into the fields already split
  size_t jobs = 0;
  for (size_t i = 3; i < at;) {
    int argc = atoi(line[i]);
    if (argc <= 0) {
      break;
    }
    jobs++;
    i += (size_t)argc + 1;
  }
  char*** argvs = malloc((jobs ? jobs : 1) * sizeof(char**));
  size_t j = 0;
  for (size_t i = 3; i < at && j < jobs;) {
    int argc = atoi(line[i]);
    char** argv = malloc(((size_t)argc + 1) * sizeof(char*));
    for (int k = 0; k < argc; k++) {
      argv[k] = line[i + 1 + (size_t)k];
    }
    argv[argc] = NULL;
    argvs[j++] = argv;
    i += (size_t)argc + 1;
  }

  pid_t* pids = malloc((jobs ? jobs : 1) * sizeof(pid_t));
  int* codes = malloc((jobs ? jobs : 1) * sizeof(int));
  for (size_t i = 0; i < jobs; i++) {
    pids[i] = -1;
    codes[i] = 127;
  }

  size_t next = 0;
  int live = 0;
  while (next < jobs || live > 0) {
    while (next < jobs && live < width) {
      char path[4096];
      snprintf(path, sizeof(path), "%s/%zu", dir, next);
      pid_t pid = fork();
      if (pid == 0) {
        int out = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
        int nul = open("/dev/null", O_RDONLY);
        dup2(nul, 0);
        dup2(out, 1);
        dup2(out, 2);
        execvp(argvs[next][0], argvs[next]);
        _exit(127);
      }
      pids[next] = pid;
      if (pid > 0) {
        live++;
      }
      next++;
    }
    if (live > 0) {
      int status = 0;
      pid_t done = wait(&status);
      if (done < 0) {
        break;
      }
      int slot = ezrun_par_slot(pids, (int)jobs, done);
      if (slot >= 0) {
        codes[slot] = WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
      }
      live--;
    }
  }

  // the statuses in the order the jobs were given, one to a line
  size_t cap = jobs * 8 + 2;
  char* out = malloc(cap);
  size_t len = 0;
  for (size_t i = 0; i < jobs; i++) {
    len += (size_t)snprintf(out + len, cap - len, i + 1 < jobs ? "%d\n" : "%d", codes[i]);
  }

  for (size_t i = 0; i < jobs; i++) {
    free(argvs[i]);
  }
  free(codes);
  free(pids);
  free(argvs);
  free(line);
  free(cmd);
  Term s = io_str(e, out, len);
  free(out);
  return s;
}

static void __attribute__((constructor)) ezrun_par_use(void) {
  io_eff(CID_EZRUN_PAR, ezrun_par_run, 0);
}
