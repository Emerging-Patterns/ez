# tests/fixture/bolt.bend: how bolt lints the walk fixture. It is ez's own
# bolt.bend, restated because the nearest one wins whole, with one rule off:
# `param`. The fixture's bytes are the package pkg/tests/walk.bend pins by the
# hash the hub minted for them, so a rename here is a new hash, not a style
# fix. This file is not imported, so it is not part of that package.
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

# a parameter shorter than two characters: the fixture's `x` stays
def param() -> String:
  "off"

# as in ez's bolt.bend: `law` and `closed` wait for the RFC's law phases
def laws() -> String:
  "warn"

# an `@unsafe` def that a LAWS.bend or PROOF.bend reaches
def unsafe() -> String:
  "error"
