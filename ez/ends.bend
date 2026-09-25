# ez/ends: how the commands that are not planners end. `ez check` and
# `ez build` start one bend and end on its answer; `ez test` and `ez prove`
# start one per file and end on the count. Each ends with a `P.Outcome`, the
# same end a planner's plan has, and the interpreter exits with its
# `P.status` (`Run.end`), so the status each exits with is a law (EZ-OUT-1).
# That the answer is what bend printed is EZ-TRUST-2. `ez run` reads no
# answer: it exits with the program's own status (`code` in ez/start.bend).
import Base
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R
import ../lock/plan.bend as P

# a command that ends on whether it passed: success, or a refusal whose
# reason was already printed
def outcome.of(passed: Bool) -> P.Outcome:
  Bool.pick(P.Outcome, passed, P.Success{}, P.Refused{""})

# `ez lock --package NAME` without `--upgrade` is a line ez refuses before it
# reads anything, since `--package` only filters an upgrade
def lock.flags(up: Bool, +name: String) -> P.Outcome:
  Bool.pick(P.Outcome, Bool.or(up, String.is_empty(name)), P.Success{},
    P.Refused{"ez: --package needs --upgrade"})

# `ez build`: bend exited 0
def ran(+out: String) -> P.Outcome:
  outcome.of(R.ok(out))

# `bend f -o out` checks without running main. A clean file prints nothing at
# all, and a library entry, having no main, checks clean and then exits 1 with
# "no main to run" from the emit. A check failure throws before the emit, so
# that message can only follow a check that passed.
#
# It is matched as a whole line, because that is the shape of the thing being
# claimed: bend prints it as `Error: no main to run` and nothing else. Asked as
# a substring of the whole output, the same words appearing anywhere (inside
# some other error's text, or in a source line bend echoed back while
# reporting on it) would answer yes and mean nothing, and a failing check
# would read as a passing one. Two other line-shaped facts in this tree were
# being asked of whole files the same way, and one of them silently dropped a
# test before it was caught.
def no.main(+line: String) -> Bool:
  String.eq(line, "Error: no main to run")

# whether any line of the output is that one. The rest of the walk is bound
# before the `Bool.or` rather than written under it: `Bool.or` is an ordinary
# function and reduces both sides, so a recursive call sitting inside one is
# not a branch the condition can decline. Bound first it is a plain fold over
# a handful of lines, which is what the rest of this tree does too.
def said.no.main(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      +rest = said.no.main(t)
      Bool.or(no.main(h), rest)

# whether `ez check` passed: bend exited 0, or said only that there is no main
def check.passed(+out: String) -> Bool:
  Bool.or(R.ok(out), said.no.main(String.lines(R.text(out))))

# `ez check`
def checked(+out: String) -> P.Outcome:
  outcome.of(check.passed(out))

# `ez test` and `ez prove`: every file passed
def counted(+passed: Nat, +total: Nat) -> P.Outcome:
  outcome.of(Nat.is_eq(passed, total))
