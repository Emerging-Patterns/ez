# hub: the proofs. `bend PROOF.bend` is the gate.
#
# Each law is a computation: whatever the url and body, both sides are a
# known Got or a known miss reason, so they reduce to the same value and
# the proof is the computation itself.
import Base
import ./LAWS.bend as Laws

def Laws.judge_have(_url, _body):
  {==}

def Laws.judge_refuse(_url, _body):
  {==}

def Laws.judge_miss(_good, _url, _body):
  {==}
