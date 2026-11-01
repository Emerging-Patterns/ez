# When an upgrade moves a hash, every line of a `.bend` file outside `.ez` and
# `.git` that starts `import <old>/` names `<new>` afterwards.
#
# This guarantee and laws/RewriteKeepsOtherLines.bend are proved for the
# moves an upgrade makes (`moves.ok`, laws/defs/WorldAfterLock.bend): each
# old hash names something, no hash holds `/` or a newline, as a `0x` name
# never does, and no move's new hash is the old hash of a move after it.
# That last is the premise the spec's notes call for: swaps apply one after
# another, so a new hash that is a later move's old one would be moved
# again. The text laws are over `U.reimport.many`, and the plan laws carry
# them to what `ez lock --upgrade` leaves at a `.bend` source it read and
# the World names once (`found`, with `pre` and `post` around it), when the
# lock does not refuse; that the sources the upgrade reads are the `.bend`
# files outside `.ez` and `.git` is the interpreter's (trusted in
# src/ez/app.bend). A line names a hash when it starts `import <hash>/` at
# column 0; the new hash a line names is the one the first move of its old
# hash sends it to.
import Base
import ../src/ledger/upgrade.bend as U
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ./defs/LockInputs.bend as D1
import ./defs/WorldAfterLock.bend as D2

# the hash a list of moves sends an old hash to: the first move of it
def moved.to(ss: List<&2, U.Swap>, +old: String) -> Maybe<&2, String>:
  match ss:
    case []:
      None{}
    case U.Swap{o, n} <> t:
      +rest = moved.to(t, old)
      Bool.pick(Maybe<&2, String>, String.eq(o, old), Some{n}, rest)

# LAW: when an upgrade moves a hash, every line of a source that starts
# `import <old>/` starts `import <new>/` afterwards, `<new>` being where the
# first move of `<old>` sends it
law rewrite_names_new:
  for +ss: List<&2, U.Swap>
  for +text: String
  for +i: Nat
  for +old: String
  for +new: String
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for +to: {moved.to(ss, old) == Some{new} : Maybe<&2, String>}
  for hit: {String.starts_with(D2.line.at(String.lines(text), i), U.reimport.head(old))
    == True{} : Bool}
  {String.starts_with(D2.line.at(String.lines(U.reimport.many(ss, text)), i),
    U.reimport.head(new)) == True{} : Bool}

# LAW: so when an upgrade moves a hash, every line of such a source that
# starts `import <old>/` starts `import <new>/` afterwards, for the moves an
# upgrade makes (`moves.ok`)
law upgrade_rewrites_imports:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {D1.found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {D2.found.miss(pre, at) == True{} : Bool}
  for +mq: {D2.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  for +i: Nat
  for +old: String
  for +new: String
  for +mv: {D2.moves.ok(D2.swaps(w)) == True{} : Bool}
  for +to: {moved.to(D2.swaps(w), old) == Some{new} : Maybe<&2, String>}
  for hit: {String.starts_with(D2.line.at(String.lines(text), i), U.reimport.head(old))
    == True{} : Bool}
  {String.starts_with(D2.line.at(String.lines(D2.left.at(P.put(w, at), text)), i),
    U.reimport.head(new)) == True{} : Bool}
