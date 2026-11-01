# Every command exits 0 on success and 1 on any failure ez detects, except `ez
# run` and `ez tool run`, which exit with the program's status.
#
# This guarantee is proved for every command, each over the end its planner,
# or the pure half of its interpreter, gives it. A planner's plan ends with
# an outcome, and `P.status` is the status the interpreter exits with
# (`Run.end`): `ez init`, `ez add`, `ez remove`, `ez lock`, plain or
# `--upgrade`, `ez fetch`, `ez publish` and `ez doctor` exit 1 exactly when
# their planner refuses, or for doctor fails the command, and 0 when it does
# not (`init_exits_as_it_refuses`, `add_exits_as_it_refuses`,
# `remove_exits_as_it_refuses`, `lock_exits_as_it_refuses`,
# `fetch_exits_as_it_refuses`, `pub_exits_as_it_refuses`,
# `doctor_exits_as_it_fails`). `ez tool run`, `install` and `upgrade` exit
# with `TP.code` of the plan's end and the status of the program the plan
# started: a refusal exits 1 whatever a program would have said, since none
# is started (`tool_refusal_status_one`), `ez tool run` that goes on exits
# with the program's status (`tool_run_status_is_program`), and `install`
# and `upgrade` that go on exit 0 (`tool_link_status_zero`). `ez tool sync`
# exits 1 exactly when it refuses (`sync_exits_as_it_refuses`), which it
# does with no ez.toml (`sync_needs_ledger`); each install it runs ends as
# `ez tool install` does, so the first that refuses ends the sync with 1.
# `ez check`, `ez build`, `ez run`, `ez test` and `ez prove` are not
# planners. `ez check`, `ez build` and `ez run` first decide from ez.toml
# what to start (`src/ez/start.bend`): with no ez.toml, or one that does not
# parse, each refuses, starts nothing and exits 1 (`start_needs_ledger`,
# `start_needs_parse`). `ez check`, `ez build`, `ez test` and `ez prove` end
# with an outcome `src/ez/ends.bend` makes from what bend answered, and exit
# 1 exactly when the check did not pass, bend did not exit 0, or a file did
# not pass (`check_exits_as_it_passes`, `build_exits_as_bend`,
# `gate_exits_as_it_counts`). `ez run` exits with `S.code` of what it
# decided and the status of the program it started: 1 for a refusal, since
# none is started (`run_refusal_exits_one`), and the program's own status
# otherwise, as `cargo run` does (`run_exits_with_program`); a program bend
# could not check is bend's failure, and exits with bend's status. `ez lock
# --package` without `--upgrade` exits 1 before anything is read
# (`package_needs_upgrade`). Before any command runs, `src/ez/line.bend`
# decides how the line ends. Help exits 0: a bare `ez`, a line that selected
# no command, and every request for help Shake answers (`bare_exits_zero`,
# `help_exits_zero`). A misused line exits 1: a bare group such as `ez
# tool`, and every line Shake refuses, an unknown command or flag, a word
# too many, a missing argument or value, an option given twice, or `ez help`
# of a word that names no command there, which Shake refuses as `Unexpected`
# rather than answering as a request for help (`group_exits_one`,
# `usage_error_exits_one`; the last case is shake's
# laws/HelpWordAsksForHelp.bend, trusted in src/ez/line.bend). A line that
# names a command runs it, with the bindings Shake made for that command,
# and leaves the status to it (`command_runs`, `command_ends_its_own`). What
# the laws take from the interpreter is trusted in src/ez/app.bend: that it
# exits with the status these functions give; that it hands `TP.code` the
# status the program exited with, and `S.code` the status bend exited with,
# 128 plus the signal for one a signal ended and 127 for one that could not
# be started; that a failure it meets itself, a write the system rejects, a
# build or link that fails, a fetch inside `ez tool`, or a loop that runs
# out of fuel, exits 1; and that the answer `src/ez/ends.bend` reads is what
# bend printed and the status it exited with. A word the native runtime
# takes is not ez's: since bend 2.0.38 the runtime takes `+RTS`, `-RTS` and
# the words between them, and the first `--RTS`, before ez sees them
# (trusted in src/share/args.bend), so `ez +RTS --threads 4 -RTS lock` runs
# `ez lock` on four threads. Every other word is ez's: `--threads`, `--gpu`,
# `--gpu-build` and `--bend-help` are flags no command declares, which Shake
# refuses, exiting 1 by `usage_error_exits_one`, and a `--` is Shake's to
# read. `--help` reaches ez, and Shake reads it as it reads `help`: before
# any positional of the command is bound, `ez --help` and `ez add --help`
# are requests for help, exiting 0 by `help_exits_zero`, while `ez add
# owner/repo --help` is a usage error (shake's
# laws/HelpWordAsksForHelp.bend, trusted in src/ez/line.bend). A `--help`
# after a `--` is a word like any other, and one among the words `ez run`
# and `ez tool run` forward is the program's.
#
# The statuses a line exits with before any command runs (src/ez/line.bend)
# and the ends of the commands that are not planners (src/ez/ends.bend) are
# stated here, and so are what `ez check`, `ez build` and `ez run` start
# (src/ez/start.bend) and the status `ez run` exits with.
import Base
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/lock/plan.bend as P
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/relock.bend as AR
import ../src/relock/relock.bend as R
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../src/init/plan.bend as IP
import ../src/remove/plan.bend as RP
import ../src/remove/relock.bend as RR
import ../src/ws/relock.bend as Rel
import 0xa383b26a5a0ef35663b3615d7aedf9e3/main.bend as Shake
import ../src/ez/line.bend as LLine
import ../src/ez/ends.bend as EEnds
import ../src/ez/start.bend as S
import 0x8e26a6f8c31689519e618374376ee3dd/src/answer.bend as RAnswer
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# LAW: `ez publish` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
law pub_exits_as_it_refuses:
  for +w: PW.World
  {P.code(PP.plan(w)) == P.status.of(PP.refuses(w)) : U32}

# LAW: `ez doctor` ends with the status of its plan's outcome, which is 1
# exactly when it fails the command and 0 when it does not
law doctor_exits_as_it_fails:
  for +w: DW.World
  {P.code(DP.plan(w)) == P.status.of(DP.refuses(w)) : U32}

# LAW: `ez lock`, plain or `--upgrade`, ends with the status of its plan's
# outcome, which is 1 exactly when it refuses and 0 when it does not
law lock_exits_as_it_refuses:
  for +w: W.World
  {P.code(P.plan(w)) == P.status.of(P.refuses(w)) : U32}

# LAW: `ez add` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
law add_exits_as_it_refuses:
  for +w: A.World
  {P.code(AP.command(w)) == P.status.of(AP.refuses.command(w)) : U32}

# LAW: and ends with the status of whether it refuses
law add_whole_exits_as_it_refuses:
  for +w: AR.World
  {P.code(AR.plan(w)) == P.status.of(AR.refuses(w)) : U32}

# LAW: `ez fetch` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
law fetch_exits_as_it_refuses:
  for +w: F.World
  {P.code(FP.plan(w)) == P.status.of(FP.refuses(w)) : U32}

# LAW: `ez init` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
law init_exits_as_it_refuses:
  for +w: IP.World
  {P.code(IP.plan(w)) == P.status.of(IP.refuses(w)) : U32}

# LAW: `ez remove` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
law remove_exits_as_it_refuses:
  for +w: RP.World
  {P.code(RP.plan(w)) == P.status.of(RP.refuses(w)) : U32}

# LAW: and ends with the status of whether it refuses
law remove_whole_exits_as_it_refuses:
  for +w: RR.World
  {P.code(RR.plan(w)) == P.status.of(RR.refuses(w)) : U32}

# LAW: and ends with the status of whether it refuses
law add_ws_exits_as_it_refuses:
  for +root: Rel.Rooted
  for +w: AR.World
  {P.code(Rel.add.plan(root, w)) == P.status.of(R.refuses(Rel.add.plan(root, w))) : U32}

# LAW: and ends with the status of whether it refuses
law remove_ws_exits_as_it_refuses:
  for +root: Rel.Rooted
  for +w: RR.World
  {P.code(Rel.remove.plan(root, w)) == P.status.of(R.refuses(Rel.remove.plan(root, w))) : U32}

# ---------------------------------------------------------------------------
# line: the status a line exits with before any command runs (ez/line.bend).
# ez/app.bend exits with `LLine.status` of `LLine.line` of what Shake
# parsed, and a line that names a command runs it, whose plan's end is its
# own status.

# LAW: a request for help, `ez help` or `ez help <path>`, shows help and
# exits 0. Shake answers a request for help only for a path whose every word
# names a command under the one before it; `ez help bogus` fails as
# `Unexpected` and so is a usage error below. That is shake's guarantee
# (shake's laws/HelpWordAsksForHelp.bend, with `help_path` of its
# interface), trusted in src/ez/line.bend.
law help_exits_zero:
  for +app: Shake.Cli
  for +e: Shake.ParseErr
  for +path: List<&2, String>
  for asks: {Shake.help_path(e) == Some{path} : Maybe<&2, List<&2, String>>}
  {LLine.status(LLine.line(app, Fail{e})) == LLine.Exits{0} : LLine.Status}

# LAW: every other line Shake refuses exits 1: an unknown command or a word
# too many (`Unexpected`), `ez help` of a word that names no command there,
# an unknown flag, a missing argument or value, a value it does not allow, or
# an option given twice
law usage_error_exits_one:
  for +app: Shake.Cli
  for +e: Shake.ParseErr
  for no: {Shake.help_path(e) == None{} : Maybe<&2, List<&2, String>>}
  {LLine.status(LLine.line(app, Fail{e})) == LLine.Exits{1} : LLine.Status}

# LAW: a bare `ez`, a line that selected no command, shows help and exits 0,
# whatever Shake bound
law bare_exits_zero:
  for +app: Shake.Cli
  for +m: Shake.Matched
  for +bare: {Shake.path_of(m) == [] : List<&2, String>}
  {LLine.status(LLine.line(app, Done{m})) == LLine.Exits{0} : LLine.Status}

# LAW: a path that names no command and is not empty, a bare `ez tool`,
# exits 1
law group_exits_one:
  for +app: Shake.Cli
  for +m: Shake.Matched
  for none: {LLine.is.help(LLine.command(LLine.path(m))) == True{} : Bool}
  for some: {String.is_empty(LLine.path(m)) == False{} : Bool}
  {LLine.status(LLine.line(app, Done{m})) == LLine.Exits{1} : LLine.Status}

# LAW: a path that names a command runs that command, with what Shake bound
# for that command (`LLine.leaf`: its Matched, at the end of the selected path)
law command_runs:
  for +app: Shake.Cli
  for +m: Shake.Matched
  for named: {LLine.is.help(LLine.command(LLine.path(m))) == False{} : Bool}
  {LLine.line(app, Done{m}) == LLine.Runs{LLine.command(LLine.path(m)), LLine.leaf(m)} : LLine.Line}

# LAW: and the line decides no status for it: the command's own end does
law command_ends_its_own:
  for +app: Shake.Cli
  for +m: Shake.Matched
  for named: {LLine.is.help(LLine.command(LLine.path(m))) == False{} : Bool}
  {LLine.status(LLine.line(app, Done{m})) == LLine.Ends{} : LLine.Status}

# ---------------------------------------------------------------------------
# ends: the commands that are not planners (ez/ends.bend). Each ends with an
# outcome, as a plan does, and the interpreter exits with its `P.status`.

# LAW: `ez build` exits 1 exactly when bend did not exit 0, and 0 when it did
law build_exits_as_bend:
  for +out: String
  {P.status(EEnds.ran(out)) == P.status.of(Bool.not(RAnswer.ok(out))) : U32}

# LAW: `ez check` exits 1 exactly when the check did not pass, and 0 when it
# did
law check_exits_as_it_passes:
  for +out: String
  {P.status(EEnds.checked(out)) == P.status.of(Bool.not(EEnds.check.passed(out))) : U32}

# LAW: `ez test` and `ez prove` exit 1 exactly when a file did not pass, and
# 0 when every one did
law gate_exits_as_it_counts:
  for +passed: Nat
  for +total: Nat
  {P.status(EEnds.counted(passed, total))
    == P.status.of(Bool.not(Nat.is_eq(passed, total))) : U32}

# LAW: `ez lock --package NAME` without `--upgrade` is refused, and exits 1
law package_needs_upgrade:
  for +name: String
  for ne: {String.is_empty(name) == False{} : Bool}
  {P.status(EEnds.lock.flags(False{}, name)) == 1 : U32}

# ---------------------------------------------------------------------------
# start: what `ez check`, `ez build` and `ez run` start (ez/start.bend). Each
# reads ez.toml and starts one bend on the entry it names, or refuses and
# starts nothing.

# LAW: with no ez.toml, `ez check`, `ez build` and `ez run` refuse, and say
# that `ez init` makes one
law start_needs_ledger:
  for +ask: S.Ask
  {S.start(ask, None{}) == S.Refused{S.none(ask)} : S.Start}

# LAW: with an ez.toml that does not parse, they refuse, and say why
law start_needs_parse:
  for +ask: S.Ask
  for +t: String
  for +why: String
  for bad: {M.Bad{why} == M.parse(t) : M.Read}
  {S.start(ask, Some{t}) == S.Refused{"ez: error: " ++ why} : S.Start}

# LAW: `ez run` that refused exits 1, whatever a program would have said,
# since none was started
law run_refusal_exits_one:
  for +why: String
  for +program: U32
  {S.code(S.Refused{why}, program) == 1 : U32}

# LAW: `ez run` that started the program exits with the program's status
law run_exits_with_program:
  for +line: List<&2, String>
  for +program: U32
  {S.code(S.Starts{line}, program) == program : U32}

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend: the status a tool command exits with. The
# interpreter exits with `TP.code` of the plan's end and the status of the
# program it started, 0 when it started none.

# LAW: a tool command that refuses exits 1, whatever a program would have
# exited with, since it starts none
law tool_refusal_status_one:
  for +w: TW.World
  for s: U32
  for r: {TP.refuses(w) == True{} : Bool}
  {TP.code(TP.exit(TP.plan(w)), s) == 1 : U32}

# LAW: `ez tool run` that does not refuse exits with the program's status
law tool_run_status_is_program:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  for ok: {TP.refuses(w) == False{} : Bool}
  for s: U32
  {TP.code(TP.exit(TP.plan(w)), s) == s : U32}

# LAW: `install` and `upgrade` that do not refuse exit 0
law tool_link_status_zero:
  for +w: TW.World
  for a: TW.Act
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for ok: {TP.refuses(w) == False{} : Bool}
  for s: U32
  {TP.code(TP.exit(TP.plan(w)), s) == 0 : U32}

# LAW: `ez tool sync` ends with 1 exactly when it refuses, and 0 when it
# does not. Each install it runs ends as `ez tool install` does, so one that
# refuses ends the sync there with 1.
law sync_exits_as_it_refuses:
  for +ledger: Maybe<&2, String>
  for +lock: Maybe<&2, String>
  {P.status(TP.sync.outcome(TP.sync(ledger, lock)))
    == P.status.of(TP.sync.refuses(TP.sync(ledger, lock))) : U32}

# LAW: with no ez.toml, `ez tool sync` refuses, whatever the lock says, so
# it installs nothing and exits 1
law sync_needs_ledger:
  for +lock: Maybe<&2, String>
  {TP.sync.refuses(TP.sync(None{}, lock)) == True{} : Bool}
