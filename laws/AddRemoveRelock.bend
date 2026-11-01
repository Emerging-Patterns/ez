# `ez add` and `ez remove` keep ez.lock.toml in step with the ledger they
# write, in one plan (in a workspace, the root's lock, as
# laws/WorkspaceAddRemoveRelock.bend says): an add or remove that succeeds
# runs its own effects and then exactly the plan a plain `ez lock` makes on
# the World it leaves, which is the ledger it writes, the `.bend` files `git
# ls-files` lists, and the answers the lock is given, so the lock is written
# last. A plain lock moves no pin (laws/PlainLockKeepsLedger.bend), so every
# dependency and tool the command did not touch keeps the pin it had. When
# that lock refuses, the command refuses, and so writes nothing: not
# ez.toml, not `.gitignore`, no tree and not the lock.
#
# This guarantee and laws/AddNotesUnlockedPackage.bend are proved over the
# plans `ez add` and `ez remove` run (`src/add/relock.bend`,
# `src/remove/relock.bend`), each the command's own plan joined to a plain
# lock's (`R.join`, `src/relock/relock.bend`). When the add or remove
# succeeds, the plain `ez lock` planner is run over the World it leaves,
# which holds the ledger it writes to ez.toml (`add_locks_what_it_writes`,
# `remove_locks_what_it_writes`) and asks the upgrade nothing
# (`add_relock_is_plain`, `remove_relock_is_plain`). A command that does not
# refuse runs its own effects, then, for `ez add`, the note, then exactly
# the effects of that lock's plan (`add_runs_add_then_lock`,
# `remove_runs_remove_then_lock`), so every law of the command's own plan
# above holds of what it runs, and every law of a plain lock holds of the
# lock it writes, laws/PlainLockKeepsLedger.bend's pins among them. A lock
# that refuses refuses the command (`add_refuses_with_lock`,
# `remove_refuses_with_lock`), and a refused command writes nothing
# (`add_whole_refusal_writes_nothing`,
# `remove_whole_refusal_writes_nothing`). The note is the line naming the
# added hash exactly when the lock's packages hold none under it
# (`add_notes_unlocked`, `add_notes_nothing_when_locked`); the lock's
# packages are the ones the walk from the `.bend` files git lists reaches
# (laws/LockReproducible.bend), so a package no listed file imports is not
# among them. The package `ez add` walked is handed to the lock as a tree
# read from BEND_LIB, where the add lays it, and the lock checks it as any
# tree there; that the interpreter answers the lock's other questions as `ez
# lock`'s does is trusted in src/ez/app.bend.
import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/add/plan.bend as AP
import ../src/add/relock.bend as AR
import ../src/relock/relock.bend as R
import ../src/remove/plan.bend as RP
import ../src/remove/relock.bend as RR

# ---------------------------------------------------------------------------
# the add and the lock as one plan (`AR.plan`, add/relock.bend), which is
# the plan the interpreter runs. The laws above are about the add's own plan
# (`AP.command`); `add_runs_add_then_lock` says the command runs exactly
# those effects first, so they hold of the command too.

# LAW: `ez add` that succeeds runs the add's effects, then the note, then
# exactly the effects of the plan a plain `ez lock` makes on the World the
# add leaves, which writes the lock last
law add_runs_add_then_lock:
  for +w: AR.World
  for ok: {AR.refuses(w) == False{} : Bool}
  {P.effects(AR.plan(w)) == List.append(&2, P.Effect, P.effects(AP.command(AR.add(w))),
    List.append(&2, P.Effect, AR.notes(w), P.effects(P.plan(AR.lock.world(w)))))
    : List<&2, P.Effect>}

# LAW: the World that lock reads holds the ledger the add writes to ez.toml
law add_locks_what_it_writes:
  for +w: AR.World
  for +text: String
  for put: {P.put.plan(AP.command(AR.add(w)), "ez.toml") == P.Put{text} : P.Wrote}
  {W.ledger.of(AR.lock.world(w)) == Some{text} : Maybe<&2, String>}

# LAW: and is a plain lock's, which moves no pin
# (laws/PlainLockKeepsLedger.bend)
law add_relock_is_plain:
  for +w: AR.World
  {W.args.upgrade(AR.lock.world(w)) == False{} : Bool}

# LAW: when that lock refuses, `ez add` refuses
law add_refuses_with_lock:
  for +w: AR.World
  for r: {R.refuses(P.plan(AR.lock.world(w))) == True{} : Bool}
  {AR.refuses(w) == True{} : Bool}

# ---------------------------------------------------------------------------
# the remove and the lock as one plan (`RR.plan`, remove/relock.bend), which
# is the plan the interpreter runs. The laws above are about the remove's own
# plan (`RP.plan`); `remove_runs_remove_then_lock` says the command runs
# exactly those effects first, so they hold of the command too.

# LAW: `ez remove` that succeeds runs the remove's effects, then exactly the
# effects of the plan a plain `ez lock` makes on the World the remove leaves,
# which writes the lock last
law remove_runs_remove_then_lock:
  for +w: RR.World
  for ok: {RR.refuses(w) == False{} : Bool}
  {P.effects(RR.plan(w)) == List.append(&2, P.Effect, P.effects(RP.plan(RR.remove(w))),
    P.effects(P.plan(RR.lock.world(w)))) : List<&2, P.Effect>}

# LAW: the World that lock reads holds the ledger the remove writes to ez.toml
law remove_locks_what_it_writes:
  for +w: RR.World
  for +text: String
  for put: {P.put.plan(RP.plan(RR.remove(w)), "ez.toml") == P.Put{text} : P.Wrote}
  {W.ledger.of(RR.lock.world(w)) == Some{text} : Maybe<&2, String>}

# LAW: and is a plain lock's, which moves no pin
# (laws/PlainLockKeepsLedger.bend)
law remove_relock_is_plain:
  for +w: RR.World
  {W.args.upgrade(RR.lock.world(w)) == False{} : Bool}

# LAW: when that lock refuses, `ez remove` refuses
law remove_refuses_with_lock:
  for +w: RR.World
  for r: {R.refuses(P.plan(RR.lock.world(w))) == True{} : Bool}
  {RR.refuses(w) == True{} : Bool}
