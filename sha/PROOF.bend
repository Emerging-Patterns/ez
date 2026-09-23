# sha: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../sha/sha.bend as Sha
import ../sha/nar.bend as Nar
import ../pkg/pkg.bend as K
import ../pkg/LAWS.bend as PL
import ../pkg/PROOF.bend as PP
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# by induction on the left text: its first character's bytes lead both sides,
# and the rest is the law again once the append is reassociated
def Laws.utf8_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String,
        String.append(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(String.append(t, b))),
        String.append(Sha.utf8.put(Char.to_u32(h)),
          String.append(Sha.utf8(t), Sha.utf8(b))),
        String.append(String.append(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(t)),
          Sha.utf8(b)),
        Equal.cong(String, String, x => String.append(Sha.utf8.put(Char.to_u32(h)), x),
          Sha.utf8(String.append(t, b)),
          String.append(Sha.utf8(t), Sha.utf8(b)),
          Laws.utf8_append(t, b)),
        Equal.sym(String,
          String.append(String.append(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(t)),
            Sha.utf8(b)),
          String.append(Sha.utf8.put(Char.to_u32(h)),
            String.append(Sha.utf8(t), Sha.utf8(b))),
          Eq.append_assoc(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(t), Sha.utf8(b))))

# `Nar.dir` sorts before it serializes, so this is pkg's `sort_perm` carried
# under `Nar.directory`
def Laws.nar_dir_order_free(ns, es, dis):
  Equal.cong(List<&2, K.File>, String, ys => Nar.directory(ys),
    K.file.sort(PL.perm(ns, es)), K.file.sort(es),
    PL.sort_perm(ns, es, dis))

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
