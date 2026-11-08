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

# Rules bolt 1.23 to 1.27 added or widened, which fire on code that predates
# them: `pick` (C003, a search bound above its pick: src/ws/joint.bend,
# src/ws/workspace.bend), `concat` (U004, an append passed through a
# continuation: src/check/serve.bend, src/io/file.bend) and `prefix` (U017, a
# take compared to a literal: src/tool/run.bend). They are advice until those
# six findings are fixed, and go back to their groups' level then.
def pick() -> String:
  "warn"

def concat() -> String:
  "warn"

def prefix() -> String:
  "warn"
