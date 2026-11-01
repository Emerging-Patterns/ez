# `ez lock` without `--upgrade` never writes ez.toml, and records every
# dependency's and tool's pin exactly as ez.toml has it.
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ./defs/LockInputs.bend as D1

# LAW: a plain lock never writes ez.toml
law plain_lock_keeps_ledger:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.put(w, "ez.toml") == P.Kept{} : P.Wrote}

# LAW: every package a plain lock resolves, and so every package its lock
# renders, carries the source ez.toml records for its hash. Tools are
# rendered from the ledger's `[tools.*]` alone, as `M.tools_of` reads them.
law plain_lock_pins_ledger_sources:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {D1.pinned.all(W.origins(W.ledger.of(w)), P.packs(w)) == P.packs(w)
    : List<&2, L.Pack>}
