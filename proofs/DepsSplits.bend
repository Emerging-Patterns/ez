# proofs of laws/DepsSplits.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../laws/DepsSplits.bend as Laws

# By induction on the first list, with the associativity of append carrying
# each step.
def Laws.deps_splits(as, bs):
  match as:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(String,
        String.append(Rend.dep(h), Rend.deps(List.append(&2, M.Dep, t, bs))),
        String.append(Rend.dep(h), String.append(Rend.deps(t), Rend.deps(bs))),
        String.append(String.append(Rend.dep(h), Rend.deps(t)), Rend.deps(bs)),
        Equal.cong(String, String, x => String.append(Rend.dep(h), x),
          Rend.deps(List.append(&2, M.Dep, t, bs)),
          String.append(Rend.deps(t), Rend.deps(bs)), Laws.deps_splits(t, bs)),
        Equal.sym(String,
          String.append(String.append(Rend.dep(h), Rend.deps(t)), Rend.deps(bs)),
          String.append(Rend.dep(h), String.append(Rend.deps(t), Rend.deps(bs))),
          Eq.append_assoc(Rend.dep(h), Rend.deps(t), Rend.deps(bs))))
