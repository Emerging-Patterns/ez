# bolt.bend: how bolt lints ez. Every group is an error: a finding here is a
# claim about a hand-written parser or a tree walk, and both are where ez is
# wrong or slow if it is wrong or slow anywhere. See bolt/config.bend in the
# bolt repo for the groups and levels. `pedantic` is left unset, so off, which
# is what bolt itself does.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# a pure def named by no law, a law that claims nothing, an unsafe def a law
# reaches. Two of its three rules are advice for now: `law` (a def no law
# names) and `closed` (a law with no `for` and no `==`) are the law coverage
# and the closed-law cleanup that the RFC's phase one and later phases do, and
# each goes back to an error as its phase lands. A rule set by name wins over
# its group, but `law` is a Bend keyword and cannot name a def, so the group is
# the warn and `unsafe`, the one rule that stays an error, is set by name.
def laws() -> String:
  "warn"

# an `@unsafe` def that a LAWS.bend or PROOF.bend reaches
def unsafe() -> String:
  "error"
