# proofs of laws/RootRelHere.bend
import Base
import ../src/pkg/path.bend as Path
import ../src/git/git.bend as Git
import ../laws/RootRelHere.bend as Laws
import ./lemmas/NatEqSelf.bend as M1
import ./lemmas/NatSubSelf.bend as M2

def Laws.root_rel_here(at, root, entry, e):
  Equal.cong(Nat, String,
    n => Path.climb(n, Path.dir(entry)),
    Nat.sub(Git.depth(Path.dir(at)), Git.depth(root)),
    0n,
    Equal.trans(Nat,
      Nat.sub(Git.depth(Path.dir(at)), Git.depth(root)),
      Nat.sub(Git.depth(Path.dir(at)), Git.depth(Path.dir(at))),
      0n,
      Equal.cong(Nat, Nat,
        b => Nat.sub(Git.depth(Path.dir(at)), b),
        Git.depth(root), Git.depth(Path.dir(at)),
        Equal.sym(Nat, Git.depth(Path.dir(at)), Git.depth(root),
          M1.nat_eq_is(Git.depth(Path.dir(at)), Git.depth(root), e))),
      M2.sub_self(Git.depth(Path.dir(at)))))
