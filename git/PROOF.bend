# git: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../manifest/toml.bend as T
import ../lock/lock.bend as L
import ../git/git.bend as G
import ./LAWS.bend as Laws

# The six keys are written out as literals on both sides, so every lookup in
# `L.src_of` decides against a literal and computes: `kind` finds "git", each
# named key finds the pair written for it, and `tag` runs off the end of the
# six into whatever follows. Nothing is left symbolic but the values, and they
# are carried through untouched.
def Laws.origin_read(url, rev, entry, root, nar, ts):
  {==}
