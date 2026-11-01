# `ez add` that succeeds says, after the lines the add says and before the
# lock's effects, that ez.lock.toml does not hold the package it added, naming
# its hash and `ez lock` as the step to run once a listed file imports it,
# exactly when the lock it writes holds no package under that hash, which is
# when no `.bend` file `git ls-files` lists imports it, an untracked file's
# import included. When the lock holds it, the add says nothing more.
import Base
import ../src/lock/plan.bend as P
import ../src/add/relock.bend as AR

# LAW: when the lock holds no package under the hash the add records, the
# note is the line that says so, naming the hash
law add_notes_unlocked:
  for +w: AR.World
  for no: {AR.held(P.packs(AR.lock.world(w)), AR.added(AR.add(w))) == False{} : Bool}
  {AR.notes(w) == [P.Say{AR.unlocked(AR.added(AR.add(w)))}] : List<&2, P.Effect>}

# LAW: and when it holds one, there is no note
law add_notes_nothing_when_locked:
  for +w: AR.World
  for yes: {AR.held(P.packs(AR.lock.world(w)), AR.added(AR.add(w))) == True{} : Bool}
  {AR.notes(w) == [] : List<&2, P.Effect>}
