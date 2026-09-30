# ez/timer: the clock ez/clock's budget is kept by. `date -d` works out the
# deadline at the start and `test -gt` does the one comparison at the end,
# both run through snap's foreign effect. This half lives apart from ez/clock
# because bend 2.0.32 fails a proof whose imports reach foreign code, so a law
# may import ez/clock but never this.
import Base
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ../share/env.bend as Env
import ./clock.bend as Clock

# how many seconds a whole run may take. Five minutes is what the gate is held
# to; a tree that honestly needs longer says so in EZ_DEADLINE, and "0" turns
# the budget off for someone bisecting with the cache cold.
def seconds() -> IO(String):
  Env.var("EZ_DEADLINE", "300")

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
  start.go(Clock.on(secs), secs)

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
