# ez/clock: the wall-clock budget a run has to finish inside.
#
# `ez test` is held to it, since a check nobody waits for is not one. The
# budget is a comparison like any other: it is checked, it is counted, and a run that
# overran fails on it the way a test that printed the wrong line fails. That is
# the difference between a number in a readme and a number something enforces.
#
# Base has no clock and no arithmetic over what `date` prints, and neither is
# needed. `date -d` works out the deadline at the start, and `test -gt` does
# the one comparison at the end, so nothing here parses a number. Both are
# programs ez already runs the way it runs `find` and `mkdir`, with no shell
# between.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../ez/env.bend as Env

# how many seconds a whole run may take. Five minutes is what the gate is held
# to; a tree that honestly needs longer says so in EZ_DEADLINE, and "0" turns
# the budget off for someone bisecting with the cache cold.
def seconds() -> IO(String):
  Env.var("EZ_DEADLINE", "300")

# whether a budget is being kept at all
def on(+secs: String) -> Bool:
  Bool.not(Bool.or(String.is_empty(secs), String.eq(secs, "0")))

# the second the run must be finished by, worked out once at the start so that
# nothing later has to add anything up
def by(+secs: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["date", "-d", "+" ++ secs ++ " seconds", "+%s"])
    return String.trim(R.text(out))

# the deadline, or "" when there is none
def start.go(keep: Bool, +secs: String) -> IO(String):
  match keep:
    case False{}:
      IO.pure(String, "")
    case True{}:
      by(secs)

# the deadline, or "" when there is none
def start(+secs: String) -> IO(String):
  start.go(on(secs), secs)

# whether the deadline has gone by
def over.now(+deadline: String) -> IO(Bool):
  do IO<Bool>:
    +now : String <- R.exec(["date", "+%s"])
    +cmp : String <- R.exec(["test", String.trim(R.text(now)), "-gt", deadline])
    return R.ok(cmp)

# whether the run has outstayed its budget, which a run with no budget never
# has
def over.go(none: Bool, +deadline: String) -> IO(Bool):
  match none:
    case True{}:
      IO.pure(Bool, False{})
    case False{}:
      over.now(deadline)

# whether the run has outstayed its budget, which a run with no budget never
# has
def over(+deadline: String) -> IO(Bool):
  over.go(String.is_empty(deadline), deadline)

# the deadline as the run effect wants it: an absolute second, or "0" when
# there is no budget to keep. The effect is what queues the jobs, so it is what
# keeps the deadline; a job bounded by what was left when its batch started is
# not bounded at all once it waits its turn behind three others.
def by.effect(+deadline: String) -> String:
  Bool.pick(String, String.is_empty(deadline), "0", deadline)
