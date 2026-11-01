# proofs of laws/PlainPathHasNoClimbs.bend
import Base
import ../src/pkg/path.bend as Path
import ../laws/SlashlessPathSplitsToItself.bend as L1
import ../laws/PlainPathHasNoClimbs.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

# LAW: a singleton that is not a climb counts as no climbs
law ups_plain.go:
  for +p: String
  for e2: {False{} == String.eq(p, "..") : Bool}
  {Path.ups.go([p]) == 0n : Nat}

def ups_plain.go(_p, e2):
  %e2 : {Nat.add(Bool.pick(Nat, _, 1n, 0n), Path.ups.go([])) == 0n : Nat}
  {==}

def Laws.ups_plain(p, e, e2):
  Equal.trans(Nat,
    Path.ups.go(String.split(p, '/')),
    Path.ups.go([p]),
    0n,
    Equal.cong(List<&2, String>, Nat, ps => Path.ups.go(ps),
      String.split(p, '/'), [p], L1.split_plain(p, e)),
    ups_plain.go(p, e2))
