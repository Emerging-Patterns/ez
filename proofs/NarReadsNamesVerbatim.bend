# proofs of laws/NarReadsNamesVerbatim.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/sha/nar.bend as Nar
import ../laws/NarReadsNamesVerbatim.bend as Laws

# LAW: a char that is not a NUL is the next char of the field it is in
law cut_push:
  for b: Bool
  for c: Char
  for x: String
  for fs: List<&2, String>
  for n: {Bool.not(b) == True{} : Bool}
  {Nar.cut.at(b, c, x <> fs) == SCon{c, x} <> fs : List<&2, String>}

def cut_push(b, _c, _x, _fs, n):
  match b:
    case True{}:
      Eq.bit.absurd(&2, {Nar.cut.at(True{}, _c, _x <> _fs) == SCon{_c, _x} <> _fs
        : List<&2, String>}, n)
    case False{}:
      {==}

# by induction on the field: its first char is no NUL, so it is pushed onto
# the field the rest of it reads as, and the NUL at its end starts the rest
def Laws.nar_field_verbatim(x, rest, c):
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(List<&2, String>,
        Nar.cut(String.append(t, SCon{Nar.nul(), rest})), t <> Nar.cut(rest),
        Laws.nar_field_verbatim(t, rest,
          Eq.and.right(Bool.not(Char.is_eq(h, Nar.nul())), Nar.clean(t), c)))
        : {Nar.cut.at(Char.is_eq(h, Nar.nul()), h, _) == SCon{h, t} <> Nar.cut(rest)
          : List<&2, String>}
      cut_push(Char.is_eq(h, Nar.nul()), h, t, Nar.cut(rest),
        Eq.and.left(Bool.not(Char.is_eq(h, Nar.nul())), Nar.clean(t), c))

# by induction on the fields, each read by the law above
def Laws.nar_listing_verbatim(fs, c):
  match fs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(List<&2, String>,
        Nar.cut(String.append(h, SCon{Nar.nul(), Nar.joined(t)})), h <> Nar.cut(Nar.joined(t)),
        Laws.nar_field_verbatim(h, Nar.joined(t),
          Eq.and.left(Nar.clean(h), Nar.clean.all(t), c)))
        : {_ == h <> t : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, ys => h <> ys,
        Nar.cut(Nar.joined(t)), t,
        Laws.nar_listing_verbatim(t, Eq.and.right(Nar.clean(h), Nar.clean.all(t), c)))
