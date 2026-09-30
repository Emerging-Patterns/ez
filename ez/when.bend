# ez/when: the deadline worked out and checked. `date` and `test` are
# programs, the same way `find` and `mkdir` are. `ez/clock.bend` holds the
# budget itself, which a proof can name.
import Base
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ./clock.bend as Clock

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

