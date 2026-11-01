import Base
import ../src/pkg/path.bend as Path

# LAW: a component that is none of the three the walk acts on is kept, text
# for text. This is what makes a module's name the path it was reached
# through: the normaliser rewrites `.` and `..` and copies everything else, so
# no component is ever silently folded, trimmed or cased.
law comp_name:
  for +c: String
  for e0: {False{} == String.is_empty(c) : Bool}
  for e1: {False{} == String.eq(c, ".") : Bool}
  for e2: {False{} == String.eq(c, "..") : Bool}
  {Path.comp_of(c) == Path.CName{c} : Path.Comp}
