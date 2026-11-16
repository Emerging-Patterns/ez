# proofs of laws/StepRunsThePlan.bend
import Base
import ../src/lock/plan.bend as P
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/ws/doctor.bend as WD
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../laws/StepRunsThePlan.bend as Laws

# `ez fetch`. The step and the plan take the ledger and the lock apart the
# same way, so each lemma follows one of them a level down.

# LAW: the questions decide whether the parts' plan runs, and nothing else
law fetch_asks_ran:
  for asks: List<&2, F.Ask>
  for ps: List<&2, FP.Pt>
  for +ms: List<&2, FP.Nm>
  {Laws.ran.fetch(FP.step.asks(asks, ps, ms), FP.parts.plan(ps, ms)) == FP.parts.plan(ps, ms)
    : P.Plan}

def fetch_asks_ran(asks, _ps, _ms):
  match asks:
    case []:
      {==}
    case _h <> _t:
      {==}

# LAW: and the step asks the questions it was given
law fetch_asks_asked:
  for asks: List<&2, F.Ask>
  for ps: List<&2, FP.Pt>
  for +ms: List<&2, FP.Nm>
  {Laws.asked.fetch(FP.step.asks(asks, ps, ms)) == asks : List<&2, F.Ask>}

def fetch_asks_asked(asks, _ps, _ms):
  match asks:
    case []:
      {==}
    case _h <> _t:
      {==}

# LAW: with the ledger there, the lock decides
law fetch_lock_ran:
  for got: Maybe<&2, String>
  for +world: F.World
  {Laws.ran.fetch(FP.step.lock(got, world), FP.plan.lock(got, world)) == FP.plan.lock(got, world)
    : P.Plan}

def fetch_lock_ran(got, world):
  match got:
    case None{}:
      {==}
    case Some{_text}:
      fetch_asks_ran(
        List.append(&2, F.Ask,
          FP.asks.of(FP.parts.of(F.sects(world), world), F.here(world), L.lock.hub(F.sects(world))),
          FP.names.asks(FP.name.parts.of(F.sects(world), world))),
        FP.parts.of(F.sects(world), world), FP.name.parts.of(F.sects(world), world))

# LAW: and the asks a lock leaves are what the step asks
law fetch_lock_asked:
  for got: Maybe<&2, String>
  for +world: F.World
  {Laws.asked.fetch(FP.step.lock(got, world)) == FP.wants.lock(got, world) : List<&2, F.Ask>}

def fetch_lock_asked(got, world):
  match got:
    case None{}:
      {==}
    case Some{_text}:
      fetch_asks_asked(
        List.append(&2, F.Ask,
          FP.asks.of(FP.parts.of(F.sects(world), world), F.here(world), L.lock.hub(F.sects(world))),
          FP.names.asks(FP.name.parts.of(F.sects(world), world))),
        FP.parts.of(F.sects(world), world), FP.name.parts.of(F.sects(world), world))

# LAW: and before that the ledger
law fetch_led_ran:
  for led: Bool
  for got: Maybe<&2, String>
  for +world: F.World
  {Laws.ran.fetch(FP.step.led(led, got, world), FP.plan.led(led, got, world))
    == FP.plan.led(led, got, world) : P.Plan}

def fetch_led_ran(led, got, world):
  match led:
    case False{}:
      {==}
    case True{}:
      fetch_lock_ran(got, world)

# LAW: likewise for the questions
law fetch_led_asked:
  for led: Bool
  for got: Maybe<&2, String>
  for +world: F.World
  {Laws.asked.fetch(FP.step.led(led, got, world)) == FP.wants.led(led, got, world)
    : List<&2, F.Ask>}

def fetch_led_asked(led, got, world):
  match led:
    case False{}:
      {==}
    case True{}:
      fetch_lock_asked(got, world)

def Laws.fetch_step_runs_plan(world):
  fetch_led_ran(F.ledger(world), F.lock(world), world)

def Laws.fetch_step_asks_wants(world):
  fetch_led_asked(F.ledger(world), F.lock(world), world)

# `ez doctor`: the step and the plan read the same fields of the World

# LAW: the doctor's questions decide whether its plan runs, and nothing else
law doctor_asks_ran:
  for asks: List<&2, DW.Ask>
  for +ledger: M.Read
  for +cc: String
  for +lib: String
  for lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for cs: List<&2, DP.Note>
  {Laws.ran.doctor(DP.step.asks(asks, ledger, cc, lib, lock, rs, cs),
    DP.plan.of(ledger, cc, lib, lock, rs, cs)) == DP.plan.of(ledger, cc, lib, lock, rs, cs) : P.Plan}

def doctor_asks_ran(asks, _ledger, _cc, _lib, _lock, _rs, _cs):
  match asks:
    case []:
      {==}
    case _h <> _t:
      {==}

# LAW: and the step asks the questions it was given
law doctor_asks_asked:
  for asks: List<&2, DW.Ask>
  for +ledger: M.Read
  for +cc: String
  for +lib: String
  for lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for cs: List<&2, DP.Note>
  {Laws.asked.doctor(DP.step.asks(asks, ledger, cc, lib, lock, rs, cs)) == asks : List<&2, DW.Ask>}

def doctor_asks_asked(asks, _ledger, _cc, _lib, _lock, _rs, _cs):
  match asks:
    case []:
      {==}
    case _h <> _t:
      {==}

def Laws.doctor_step_runs_plan(world):
  doctor_asks_ran(
    DP.open(List.append(&2, DW.Ask,
      DP.asks.of(DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world)),
      DP.trees.of(DW.ledger(world), DW.lock(world), DW.lock(world), DW.replies(world))),
      DW.replies(world)),
    DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world), DW.replies(world),
    DP.checked(world))

def Laws.doctor_step_asks_wants(world):
  doctor_asks_asked(
    DP.open(List.append(&2, DW.Ask,
      DP.asks.of(DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world)),
      DP.trees.of(DW.ledger(world), DW.lock(world), DW.lock(world), DW.replies(world))),
      DW.replies(world)),
    DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world), DW.replies(world),
    DP.checked(world))

# the workspace doctor passes the doctor's step on

# LAW: whatever the doctor's step, the workspace's runs the workspace's plan
law workspace_of_ran:
  for st: DP.Step
  for back: WD.Back
  for +world: DW.World
  {Laws.ran.doctor(WD.step.of(st, back, world), WD.plan(back, world)) == WD.plan(back, world)
    : P.Plan}

def workspace_of_ran(st, _back, _world):
  match st:
    case DP.Asking{_asks}:
      {==}
    case DP.Run{_pl}:
      {==}

# LAW: and asks what the doctor's asks
law workspace_of_asked:
  for st: DP.Step
  for back: WD.Back
  for +world: DW.World
  {Laws.asked.doctor(WD.step.of(st, back, world)) == Laws.asked.doctor(st) : List<&2, DW.Ask>}

def workspace_of_asked(st, _back, _world):
  match st:
    case DP.Asking{_asks}:
      {==}
    case DP.Run{_pl}:
      {==}

def Laws.workspace_doctor_step_runs_plan(back, world):
  workspace_of_ran(DP.step(world), back, world)

def Laws.workspace_doctor_step_asks(back, world):
  workspace_of_asked(DP.step(world), back, world)

# `ez publish` and `ez tool`: the step and the plan read one verdict

# LAW: whatever the publish's verdict, a step that runs runs its plan
law publish_v_ran:
  for v: PP.Verdict
  for +world: PW.World
  {Laws.ran.publish(PP.step.v(v, world), PP.plan.v(v, world)) == PP.plan.v(v, world) : P.Plan}

def publish_v_ran(v, _world):
  match v:
    case PP.Go{}:
      {==}
    case PP.Pending{_asks}:
      {==}
    case PP.Stop{_why}:
      {==}

def Laws.publish_step_runs_plan(world):
  publish_v_ran(PP.decide(world), world)

# LAW: whatever the tool command's verdict, a step that runs runs its plan
law tool_v_ran:
  for v: TP.Verdict
  for +world: TW.World
  {Laws.ran.tool(TP.step.v(v, world), TP.plan.v(v, world)) == TP.plan.v(v, world) : TP.Plan}

def tool_v_ran(v, _world):
  match v:
    case TP.Go{}:
      {==}
    case TP.Pending{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}

def Laws.tool_step_runs_plan(world):
  tool_v_ran(TP.decide(world), world)
