import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A

# The upgrade's decisions (lock/up.bend) are stated over `P.ledger.next`, the
# ledger model an upgrade renders into ez.toml, and over the questions it asks,
# `P.wants.up`. A plain lock is the World whose args say no `--upgrade`, and it
# is what these two say it is.

# LAW: a plain lock asks no upgrade question, so it asks a remote nothing but
# the tree at a rev the ledger already pins
law plain_lock_asks_no_upgrade:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.wants.up(w) == [] : List<&2, Up.Ask>}
