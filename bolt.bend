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

# the law rules: `coverage` (a def no law names) and `closed`. The group is
# advice because of `coverage`, which the RFC's later phases grow; it goes
# back to an error as the laws land. A rule set by name wins over its group.
def laws() -> String:
  "warn"

# a def no law names. Since bolt 1.26 the rule is off unless bolt.bend names
# it, so it is named here to keep ez's coverage gate on, at the group's level.
def coverage() -> String:
  "warn"

# a law in a law file with no `for`/`exs` binder, equality or not. A closed
# law claims one computed case and no guarantee, and nothing exempts one.
def closed() -> String:
  "error"
