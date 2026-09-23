# ez/pass: a program run on ez's own stdin, stdout and stderr, as `cargo run`
# runs one. Every other program ez starts goes through snap's `exec`, which
# hands the child /dev/null for stdin, holds what it prints until it exits,
# and answers both at once; that is what a command that reads the answer
# wants. `ez run` and `ez tool run` read nothing back: the program talks to
# the person, and ez only waits for it and exits with its status (`S.code`
# and `TP.code`, EZ-OUT-1).
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R

# the program and its arguments, newline separated, run with no shell between
# and nothing captured. The answer is the status it exited with: 128 plus the
# signal for one a signal ended, and 127 for one that could not be started.
def ezpass.run(cmd: String) -> IO(U32):
  import "./pass.c"
  import "./pass.js"

# a program run with its arguments, on ez's own stdio
def run(argv: List<&2, String>) -> IO(U32):
  ezpass.run(R.cmd(argv))
