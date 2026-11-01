# proofs of laws/LibJudgedAsClone.bend
import Base
import ../src/lock/lock.bend as L
import ../laws/LibJudgedAsClone.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

def Laws.lib_judged_as_clone(orgs, _hub, hash, manifest, ss):
  M1.lib_as_clone.src(L.origin(orgs, hash), hash, manifest, ss)
