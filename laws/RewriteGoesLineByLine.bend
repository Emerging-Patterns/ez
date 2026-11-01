import Base
import ../src/ledger/upgrade.bend as U
import ./defs/WorldAfterLock.bend as D1

# LAW: a source is rewritten line by line: its lines afterwards are its lines
# before, each put through every move, and no more
law rewrite_by_line:
  for +ss: List<&2, U.Swap>
  for +text: String
  for +ok: {D1.moves.ok(ss) == True{} : Bool}
  {String.lines(U.reimport.many(ss, text))
    == U.reimport.many.lines(ss, String.lines(text)) : List<&2, String>}
