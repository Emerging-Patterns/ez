# Adding a dependency to a ledger model twice is adding it once.
#
# The ledger is a file a person edits, so what matters is that a lookup
# answers with what was written for it, and that the two edits `ez add` and
# `ez remove` make are the edits they claim to be.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H

# LAW: and adding it twice with the edit `ez add` makes, the one that keeps a
# vendor bit the ledger already set, is adding it once. The second add finds
# the entry the first one wrote, so the bit it keeps is the bit the first one
# gave, and the dependency it adds is the one already there.
law add_keep_idem:
  for m: M.Manifest
  for +d: M.Dep
  {Rend.add.keep(Rend.add.keep(m, d), d) == Rend.add.keep(m, d) : M.Manifest}

# ---------------------------------------------------------------------------
# a git or path target (`AP.plan`)

# LAW: `ez add` that does not refuse writes to ez.toml exactly the ledger
# `Rend.add.keep` gives with the dependency it records, the edit
# `add_keep_idem` says is the same done twice
law add_edits_ledger:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  {P.put.plan(AP.plan(w), "ez.toml")
    == P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))} : P.Wrote}

# LAW: an add that does not refuse writes to ez.toml exactly the ledger
# `Rend.add.keep` gives with the dependency it records
law add_named_edits_ledger:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {H.refuses(w) == False{} : Bool}
  {P.put.plan(H.plan(w), "ez.toml")
    == P.Put{Rend.show(Rend.add.keep(m, H.added(w)))} : P.Wrote}
