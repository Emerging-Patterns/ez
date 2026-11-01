# Import rewriting leaves every other line of every file byte-identical, and
# does not write a file with no matching line.
import Base
import ../src/ledger/upgrade.bend as U
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ./defs/LockInputs.bend as D1
import ./defs/WorldAfterLock.bend as D2

# whether a line names none of the old hashes of a list of moves
def names.none(ss: List<&2, U.Swap>, +line: String) -> Bool:
  match ss:
    case []:
      True{}
    case U.Swap{o, _n} <> t:
      +rest = names.none(t, line)
      Bool.and(Bool.not(String.starts_with(line, U.reimport.head(o))), rest)

# whether no line of a list names an old hash of a list of moves
def names.none.all(+ss: List<&2, U.Swap>, ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case h <> t:
      +rest = names.none.all(ss, t)
      Bool.and(names.none(ss, h), rest)

# LAW: and every other line is left byte for byte as it was
law rewrite_keeps_other_lines:
  for +ss: List<&2, U.Swap>
  for +text: String
  for +i: Nat
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  for miss: {names.none(ss, D2.line.at(String.lines(text), i)) == True{} : Bool}
  {D2.line.at(String.lines(U.reimport.many(ss, text)), i)
    == D2.line.at(String.lines(text), i) : String}

# LAW: and no line is added or dropped
law rewrite_keeps_line_count:
  for +ss: List<&2, U.Swap>
  for +text: String
  for +ok: {D2.moves.ok(ss) == True{} : Bool}
  {List.length(&2, String, String.lines(U.reimport.many(ss, text)))
    == List.length(&2, String, String.lines(text)) : Nat}

# LAW: a source none of whose lines names a moved hash comes back byte for
# byte, newline or none at its end, so the upgrade has nothing to write
law rewrite_nothing_named:
  for +ss: List<&2, U.Swap>
  for +text: String
  for none: {names.none.all(ss, String.lines(text)) == True{} : Bool}
  {U.reimport.many(ss, text) == text : String}

# LAW: and every other line of it is left byte for byte as it was
law upgrade_leaves_other_lines:
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
  for +mv: {D2.moves.ok(D2.swaps(w)) == True{} : Bool}
  for miss: {names.none(D2.swaps(w), D2.line.at(String.lines(text), i)) == True{} : Bool}
  {D2.line.at(String.lines(D2.left.at(P.put(w, at), text)), i)
    == D2.line.at(String.lines(text), i) : String}

# LAW: and no line is added or dropped
law upgrade_keeps_line_count:
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
  for +mv: {D2.moves.ok(D2.swaps(w)) == True{} : Bool}
  {List.length(&2, String, String.lines(D2.left.at(P.put(w, at), text)))
    == List.length(&2, String, String.lines(text)) : Nat}

# LAW: and a source none of whose lines names a moved hash is not written
law upgrade_writes_only_hits:
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
  for none: {names.none.all(D2.swaps(w), String.lines(text)) == True{} : Bool}
  {P.put(w, at) == P.Kept{} : P.Wrote}
