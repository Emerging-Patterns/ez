# add: the proofs. `bend PROOF.bend` is the gate.
#
# The plan is `plan.v(decide(w), w)`: `decide` settles what is refused or
# still asked before the walk, and on `Go` the plan is `made`, which seals the
# effects of the walk with how it ends (`outcome.k`). A sealed plan that
# refuses has no effect, so the refusal law is two case splits. A plan that
# does not refuse is therefore `Plan{effects.k(walked(w), w), Success}` with
# `outcome.k` a success (`succeeds`), and every law about what an add writes
# is a law about `effects.k`, whose one arm that is not empty is the walk's
# package.
import Base
import ./world.bend as A
import ./plan.bend as AP
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/up.bend as Up
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/ignore.bend as I
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as Git
import ../ez/target.bend as Tgt
import ../ez/named.bend as Named
import ../sha/sha.bend as Sha
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../pkg/PROOF.bend as Pk
import ./LAWS.bend as Laws

# ---------------------------------------------------------------------------
# refusals

# LAW: a sealed plan that refuses writes nothing
law seal_quiet:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for r: {AP.refuses.plan(AP.seal(es, o)) == True{} : Bool}
  {P.writes(AP.seal(es, o)) == False{} : Bool}

def seal_quiet(es, o, r):
  match o:
    case P.Success{}:
      Eq.bit.absurd(&2, {P.writes(AP.seal(es, P.Success{})) == False{} : Bool}, r)
    case P.Refused{_why}:
      {==}

# LAW: nor does any plan for a verdict that refuses
law plan_quiet:
  for v: AP.Verdict
  for +w: A.World
  for r: {AP.refuses.plan(AP.plan.v(v, w)) == True{} : Bool}
  {P.writes(AP.plan.v(v, w)) == False{} : Bool}

def plan_quiet(v, w, r):
  match v:
    case AP.Go{}:
      seal_quiet(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), r)
    case AP.Wait{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

def Laws.add_refusal_writes_nothing(w, r):
  plan_quiet(AP.decide(w), w, r)

# No ledger reads as the `Bad` arm, which stops before anything is asked.
def Laws.add_needs_ledger(_a, _here, _home, _ignore, _rs):
  {==}

def Laws.add_needs_ledger_asks_nothing(_a, _here, _home, _ignore, _rs):
  {==}

# The read is rewritten to the `Bad` the premise gives, which stops.
def Laws.add_refuses_unread(a, here, home, s, ignore, rs, _why, bad):
  %bad : {AP.refuses.plan(AP.plan.v(AP.decide.read(_, A.World{a, here, home, Some{s},
    ignore, rs}), A.World{a, here, home, Some{s}, ignore, rs})) == True{} : Bool}
  {==}
