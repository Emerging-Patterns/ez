# proofs of laws/ReaddedSourceKeepsName.bend
import Base
import ../laws/ReaddedSourceKeepsName.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

def Laws.had_keeps(n, h, en, url, rev, tag, root, nar, vend, t, fresh):
  M1.had_first(n, h, en, url, rev, tag, root, nar, vend, t, fresh)
