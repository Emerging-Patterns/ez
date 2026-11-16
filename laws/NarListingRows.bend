# The NAR walk reads its listing five fields to a path: the type, the mode,
# the name, the path from the top and a symlink's target, in that order, and
# a path the listing cut short is not read at all. This is internal: it holds
# src/sha/nar.bend's reading of `find`'s output in place.
# also rests on: laws/NarReadsNamesVerbatim.bend
import Base
import ../src/sha/nar.bend as Nar

# LAW: five fields make one path, in the order `find` prints them, and the
# rest of the listing is read the same way
law rows_by_five:
  for kind: String
  for mode: String
  for name: String
  for at: String
  for target: String
  for rest: List<&2, String>
  {Nar.rows(kind <> (mode <> (name <> (at <> (target <> rest)))))
    == Nar.Row{kind, mode, name, at, target} <> Nar.rows(rest) : List<&2, Nar.Row>}

# LAW: a path the listing cut short, four fields with no fifth, is not read
law rows_cut_short:
  for kind: String
  for mode: String
  for name: String
  for at: String
  {Nar.rows([kind, mode, name, at]) == [] : List<&2, Nar.Row>}
