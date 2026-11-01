# proofs of laws/ExitStatusSaysFailure.bend
#
# The quantified half is a hypothesis rewritten into the one `Bool.pick` or
# `Bool.and` the code branches on, or a prefix test that `starts_append`
# already holds. The rest is a closed computation: both sides are a known
# string or list, so they reduce to the same value and the proof is the
# computation itself.
import Base
import ../src/check/eq.bend as Eq
import ../src/relock/relock.bend as R
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/pub/plan.bend as PP
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/relock.bend as AR
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
import ../laws/ExitStatusSaysFailure.bend as Laws
import ../laws/ToolRunExitsWithProgram.bend as L1
import ./lemmas/LockPlannerFacts.bend as M1

# LAW: a plan ends with the status of whether it refuses
law join_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(R.refuses(pl)) : U32}

def join_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend

# LAW: a plan ends with the status of whether it does not succeed
law plan_code_pub:
  for pl: P.Plan
  {P.code(pl) == P.status.of(Bool.not(PP.succeeds.plan(pl))) : U32}

def plan_code_pub(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.pub_exits_as_it_refuses(w):
  plan_code_pub(PP.plan(w))

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend

# LAW: a plan ends with the status of whether it fails the command
law plan_code_doctor:
  for pl: P.Plan
  {P.code(pl) == P.status.of(DP.refuses.plan(pl)) : U32}

def plan_code_doctor(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.doctor_exits_as_it_fails(w):
  plan_code_doctor(DP.plan(w))

# LAW: a plan made from what was decided ends with the status of that
# decision, whatever the upgrade decided around it
law made_code:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  {P.code(P.made(nx, cs, js, d)) == P.status.of(P.refuses.doc(d)) : U32}

def made_code(_nx, _cs, _js, d):
  match d:
    case P.Doc{_text}:
      {==}
    case P.Stop{_why}:
      {==}

def Laws.lock_exits_as_it_refuses(w):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      made_code(W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}))

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend

# LAW: a plan ends with the status of whether it refuses
law plan_code_add:
  for pl: P.Plan
  {P.code(pl) == P.status.of(AP.refuses.plan(pl)) : U32}

def plan_code_add(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.add_exits_as_it_refuses(w):
  plan_code_add(AP.command(w))

def Laws.add_whole_exits_as_it_refuses(w):
  join_code(AR.plan(w))

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend

# LAW: a plan ends with the status of whether it refuses
law plan_code_fetch:
  for pl: P.Plan
  {P.code(pl) == P.status.of(FP.refuses.plan(pl)) : U32}

def plan_code_fetch(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.fetch_exits_as_it_refuses(w):
  plan_code_fetch(FP.plan(w))

# LAW: a plan ends with the status of whether it refuses
law plan_code_init:
  for pl: P.Plan
  {P.code(pl) == P.status.of(IP.refuses.plan(pl)) : U32}

def plan_code_init(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.init_exits_as_it_refuses(w):
  plan_code_init(IP.plan(w))

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend

# LAW: a plan ends with the status of whether it refuses
law plan_code_remove:
  for pl: P.Plan
  {P.code(pl) == P.status.of(RP.refuses.plan(pl)) : U32}

def plan_code_remove(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.remove_exits_as_it_refuses(w):
  plan_code_remove(RP.plan(w))

def Laws.remove_whole_exits_as_it_refuses(w):
  join_code(RR.plan(w))

def Laws.add_ws_exits_as_it_refuses(root, w):
  join_code(Rel.add.plan(root, w))

def Laws.remove_ws_exits_as_it_refuses(root, w):
  join_code(Rel.remove.plan(root, w))

# ---------------------------------------------------------------------------
# line: each law is the premise rewritten into the one match `LLine.line` turns
# on, or, for a parse error, a case split on the error

def Laws.help_exits_zero(app, e, path, asks):
  %Equal.sym(Maybe<&2, List<&2, String>>, Shake.help_path(e), Some{path}, asks)
    : {LLine.status(LLine.line.err(_, app, e)) == LLine.Exits{0} : LLine.Status}
  {==}

def Laws.usage_error_exits_one(app, e, no):
  %Equal.sym(Maybe<&2, List<&2, String>>, Shake.help_path(e), None{}, no)
    : {LLine.status(LLine.line.err(_, app, e)) == LLine.Exits{1} : LLine.Status}
  {==}

def Laws.bare_exits_zero(app, m, bare):
  %Equal.sym(List<&2, String>, Shake.path_of(m), [], bare)
    : {LLine.status(LLine.line.run(LLine.is.help(LLine.command(String.join(_, "/"))),
        LLine.command(String.join(_, "/")), app, m)) == LLine.Exits{0} : LLine.Status}
  %Equal.sym(List<&2, String>, Shake.path_of(m), [], bare)
    : {LLine.status(LLine.line.group(String.is_empty(String.join(_, "/")), app, m))
        == LLine.Exits{0} : LLine.Status}
  {==}

def Laws.group_exits_one(app, m, none, some):
  %Equal.sym(Bool, LLine.is.help(LLine.command(LLine.path(m))), True{}, none)
    : {LLine.status(LLine.line.run(_, LLine.command(LLine.path(m)), app, m)) == LLine.Exits{1} : LLine.Status}
  %Equal.sym(Bool, String.is_empty(LLine.path(m)), False{}, some)
    : {LLine.status(LLine.line.group(_, app, m)) == LLine.Exits{1} : LLine.Status}
  {==}

def Laws.command_runs(app, m, named):
  %Equal.sym(Bool, LLine.is.help(LLine.command(LLine.path(m))), False{}, named)
    : {LLine.line.run(_, LLine.command(LLine.path(m)), app, m)
      == LLine.Runs{LLine.command(LLine.path(m)), LLine.leaf(m)} : LLine.Line}
  {==}

def Laws.command_ends_its_own(app, m, named):
  Equal.cong(LLine.Line, LLine.Status, l => LLine.status(l), LLine.line(app, Done{m}),
    LLine.Runs{LLine.command(LLine.path(m)), LLine.leaf(m)}, Laws.command_runs(app, m, named))

# ---------------------------------------------------------------------------
# ends: each command's outcome is `EEnds.outcome.of` of whether it passed,
# so one case split on that bit answers for all of them

# LAW: an outcome made from a bit ends with the status of its negation
law outcome_status:
  for b: Bool
  {P.status(EEnds.outcome.of(b)) == P.status.of(Bool.not(b)) : U32}

def outcome_status(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.build_exits_as_bend(out):
  outcome_status(RAnswer.ok(out))

def Laws.check_exits_as_it_passes(out):
  outcome_status(EEnds.check.passed(out))

def Laws.gate_exits_as_it_counts(passed, total):
  outcome_status(Nat.is_eq(passed, total))

def Laws.package_needs_upgrade(name, ne):
  %Equal.sym(Bool, String.is_empty(name), False{}, ne)
    : {P.status(Bool.pick(P.Outcome, Bool.or(False{}, _), P.Success{},
      P.Refused{"ez: --package needs --upgrade"})) == 1 : U32}
  {==}

# ---------------------------------------------------------------------------
# start: `S.start` of a ledger that is there reads it, so each law about a
# parsed ledger is its hypothesis put in place of `M.parse(t)`, and the rest
# is computation. A named entry needs its emptiness too, for `S.entry.or`.

def Laws.start_needs_ledger(_ask):
  {==}

def Laws.start_needs_parse(ask, _t, why, bad):
  %bad : {S.read(ask, _) == S.Refused{"ez: error: " ++ why} : S.Start}
  {==}

def Laws.run_refusal_exits_one(_why, _program):
  {==}

def Laws.run_exits_with_program(_line, _program):
  {==}

# ---------------------------------------------------------------------------
# laws/ExitStatusSaysFailure.bend

def Laws.tool_refusal_status_one(w, s, r):
  Equal.cong(TP.Exit, U32, e => TP.code(e, s), TP.exit(TP.plan(w)), TP.Refusal{},
    L1.tool_refusal_exits_one(w, r))

def Laws.tool_run_status_is_program(w, args, act, ok, s):
  Equal.cong(TP.Exit, U32, e => TP.code(e, s), TP.exit(TP.plan(w)), TP.Exits{TP.out(w), args},
    L1.tool_run_exits_with_program(w, args, act, ok))

# LAW: a linking act ends a plan that goes on without a program
law link_ends_a:
  for a: TW.Act
  for +w: TW.World
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.exit.of(TP.finish.of(a, w)) == TP.Finished{} : TP.Exit}

def link_ends_a(a, w, l):
  match a:
    case TW.Run{args}:
      Eq.bit.absurd(&2, {TP.exit.of(TP.finish.of(TW.Run{args}, w)) == TP.Finished{}
        : TP.Exit}, l)
    case TW.Install{}:
      {==}
    case TW.Upgrade{}:
      {==}

# LAW: so `made` for `install` or `upgrade` ends without a program
law link_ends:
  for a: TW.Act
  for +w: TW.World
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  {TP.exit(TP.made(w)) == TP.Finished{} : TP.Exit}

def link_ends(a, w, act, l):
  %Equal.sym(TW.Act, TW.act(w), a, act)
    : {TP.exit.of(TP.finish.of(_, w)) == TP.Finished{} : TP.Exit}
  link_ends_a(a, w, l)

def Laws.tool_link_status_zero(w, a, act, l, ok, s):
  Equal.cong(TP.Exit, U32, e => TP.code(e, s), TP.exit(TP.plan(w)), TP.Finished{},
    Equal.trans(TP.Exit, TP.exit(TP.plan(w)), TP.exit(TP.made(w)), TP.Finished{},
      Equal.cong(TP.Plan, TP.Exit, pl => TP.exit(pl), TP.plan(w), TP.made(w), M1.made_of(w, ok)),
      link_ends(a, w, act, l)))

# LAW: a sync ends with the status of whether it refuses
law sync_code:
  for s: TP.Sync
  {P.status(TP.sync.outcome(s)) == P.status.of(TP.sync.refuses(s)) : U32}

def sync_code(s):
  match s:
    case TP.Sync{_ns}:
      {==}
    case TP.SyncNo{_why}:
      {==}

def Laws.sync_exits_as_it_refuses(ledger, lock):
  sync_code(TP.sync(ledger, lock))

def Laws.sync_needs_ledger(_lock):
  {==}
