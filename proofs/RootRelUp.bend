# proofs of laws/RootRelUp.bend
import Base
import ../src/pkg/path.bend as Path
import ../src/git/git.bend as Git
import ../laws/RootRelUp.bend as Laws
import ./lemmas/NatEqSelf.bend as M1

# LAW: subtracting a number from one more than itself is one
law sub_succ:
  for n: Nat
  {Nat.sub(1n+n, n) == 1n : Nat}

def sub_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_succ(p)

def Laws.root_rel_up(at, root, entry, e):
  Equal.cong(Nat, String,
    n => Path.climb(n, Path.dir(entry)),
    Nat.sub(Git.depth(Path.dir(at)), Git.depth(root)),
    1n,
    Equal.trans(Nat,
      Nat.sub(Git.depth(Path.dir(at)), Git.depth(root)),
      Nat.sub(1n+Git.depth(root), Git.depth(root)),
      1n,
      Equal.cong(Nat, Nat,
        a => Nat.sub(a, Git.depth(root)),
        Git.depth(Path.dir(at)), 1n+Git.depth(root),
        M1.nat_eq_is(Git.depth(Path.dir(at)), 1n+Git.depth(root), e)),
      sub_succ(Git.depth(root))))
