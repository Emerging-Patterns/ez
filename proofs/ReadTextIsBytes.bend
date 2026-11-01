# proofs of laws/ReadTextIsBytes.bend
#
# Each law is a closed computation: both sides are a known string or a known
# IO, so they reduce to the same value and the proof is the computation
# itself.
import Base
import ../laws/ReadTextIsBytes.bend as Laws

def Laws.write_read(_s):
  {==}
