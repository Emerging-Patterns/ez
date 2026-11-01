# a number compared with itself is equal
import Base
import ../../src/check/eq.bend as Eq

# LAW: a number compared with itself is equal
law nat_eq_is:
  for a: Nat
  for b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def nat_eq_is(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Eq.bit.absurd(&2, {0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      Eq.bit.absurd(&2, {1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, nat_eq_is(p, q, e))
