# proofs of laws/HashedBodyIsHave.bend
#
# Each law is a computation: whatever the url and body, both sides are a
# known Got or a known miss reason, so they reduce to the same value and the
# proof is the computation itself.
import Base
import ../laws/HashedBodyIsHave.bend as Laws

def Laws.judge_have(_url, _body):
  {==}
