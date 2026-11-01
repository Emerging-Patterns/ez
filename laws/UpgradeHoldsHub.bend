# `ez lock --upgrade` never moves a hub dependency.
#
# The upgrade laws of phase three, for laws/UpgradeHoldsHub.bend,
# laws/UpgradeRevMovesForward.bend, laws/UpgradeOnlyNamedPackage.bend,
# laws/UpgradeTagFollows.bend and the `ez lock --upgrade` half of
# laws/GitignoreAllowlistIsLedger.bend, are stated over the ledger model the
# upgrade renders into ez.toml, and hold of the file's bytes because those
# bytes read back as that model (laws/WrittenLedgerReadsBack.bend). The
# design is in [docs/rfc/ez-lock-planner.md](docs/rfc/ez-lock-planner.md).
# laws/UpgradeHoldsHub.bend and laws/UpgradeOnlyNamedPackage.bend are proved
# so: their laws are over `P.ledger.next`, the model
# an upgrade renders, and over `P.wants.up`, the questions it asks, and what
# they say of ez.toml's bytes, and of the lock made from those bytes read
# back, holds by laws/WrittenLedgerReadsBack.bend.
# laws/UpgradeOnlyNamedPackage.bend's `NAME` is a nonempty `--package`; an
# empty one is no filter, as `ez lock --upgrade` alone.
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/add/world.bend as A

# LAW: `ez lock --upgrade` never moves a hub dependency. The entry ez.toml
# records under a name, when its source is the hub, is the entry the ledger
# the upgrade leaves records under that name, whatever `--package` named and
# whatever the remote said. A hub package's hash is its pin.
law upgrade_holds_hub:
  for +w: W.World
  for +n: String
  for hub: {M.source.is_git(M.source.dep(W.dep(w, n))) == False{} : Bool}
  {M.dep(P.ledger.next(w), n) == W.dep(w, n) : M.Dep}
