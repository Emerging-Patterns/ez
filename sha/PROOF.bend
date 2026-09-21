# sha: the proofs. `bend PROOF.bend` is the gate.
#
# Each law is a closed computation: both sides are a hex of known bytes, so
# they reduce to the same text and the proof is the computation itself.
import Base
import ./LAWS.bend as Laws

def Laws.hex_empty():
  {==}

def Laws.hex_abc():
  {==}

def Laws.hex_manifest():
  {==}
