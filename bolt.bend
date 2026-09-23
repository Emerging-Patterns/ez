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

# the law rules: `coverage` (a def no law names), `closed`, `unsafe` and
# `trace`. The group is advice because of `coverage`, which the RFC's later
# phases grow; it goes back to an error as the laws land. A rule set by name
# wins over its group, so the other three are errors below.
def laws() -> String:
  "warn"

# a law in a LAWS.bend with no `for`/`exs` binder, equality or not. A closed
# law claims one computed case and no requirement (SPEC.md), and nothing
# exempts one.
def closed() -> String:
  "error"

# an `@unsafe` def that a LAWS.bend or PROOF.bend reaches
def unsafe() -> String:
  "error"

# SPEC.md's rows and the laws' tags agree: every law a row names exists, has a
# binder and carries the row's ID, and every tag names a row SPEC.md lists.
# It is opt-in, so no group reaches it; only this def turns it on.
def trace() -> String:
  "error"
