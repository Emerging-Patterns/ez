# `ez test` counts every comparison of a run with its trailer, and passes
# exactly the ones that held: a comparison that held adds one to both the
# passes and the total, and one that did not adds one to the total alone.
# This is internal: it fixes how ez/verdict.bend keeps the score that
# ez/test.bend reports and exits on.
import Base
import ../src/ez/verdict.bend as V

# LAW: a comparison that held counts as a pass and as one more comparison
law tally_held:
  for +p: Nat
  for +n: Nat
  {V.tally(True{}, V.Tally{p, n}) == V.Tally{(1n + p : Nat), (1n + n : Nat)} : V.Tally}

# LAW: and one that did not leaves the passes as they were
law tally_failed:
  for +p: Nat
  for +n: Nat
  {V.tally(False{}, V.Tally{p, n}) == V.Tally{p, (1n + n : Nat)} : V.Tally}
