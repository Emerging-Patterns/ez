# proofs of laws/FetchRefusalWritesNothing.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/FetchRefusalWritesNothing.bend as Laws

# ---------------------------------------------------------------------------
# refusals

# LAW: a sealed plan that refuses writes nothing
law seal_quiet_fetch:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for r: {FP.refuses.plan(FP.seal(es, o)) == True{} : Bool}
  {P.writes(FP.seal(es, o)) == False{} : Bool}

def seal_quiet_fetch(es, o, r):
  match o:
    case P.Success{}:
      Eq.bit.absurd(&2, {P.writes(FP.seal(es, P.Success{})) == False{} : Bool}, r)
    case P.Refused{_why}:
      {==}

# LAW: nor does a plan for a ledger and a lock, there or not
law led_quiet:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  for r: {FP.refuses.plan(FP.plan.led(b, g, w)) == True{} : Bool}
  {P.writes(FP.plan.led(b, g, w)) == False{} : Bool}

def led_quiet(b, g, w, r):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          seal_quiet_fetch(FP.names.lay(FP.name.parts.of(F.sects(w), w),
            FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w)))),
            FP.outcome.then(FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
              FP.names.outcome(FP.name.parts.of(F.sects(w), w))),
            r)

def Laws.fetch_refusal_writes_nothing(w, r):
  led_quiet(F.ledger(w), F.lock(w), w, r)
