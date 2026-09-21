# git: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../lock/lock.bend as L
import ../git/git.bend as G
import ../pkg/path.bend as P
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# The six keys are written out as literals on both sides, so every lookup in
# `L.src_of` decides against a literal and computes: `kind` finds "git", each
# named key finds the pair written for it, and `tag` runs off the end of the
# six into whatever follows. Nothing is left symbolic but the values, and they
# are carried through untouched.
def Laws.origin_read(_url, _rev, _entry, _root, _nar, _ts):
  {==}

# The three agreement laws at the foot of LAWS.bend, which say that this
# pass's rewrites for cost did not change an answer. Each is the same
# argument: a `match` may not scrutinise a computed value, so the head's
# answer is lifted into a parameter and the law is then applied to the answer
# the code computes.

# LAW: one step of the alphabet scan
law among_agrees.arm:
  for +c: Char
  for t: List<&2, Char>
  for p: Bool
  for ih: {Laws.old.among(c, t) == G.among(c, t) : Bool}
  {Bool.or(p, Laws.old.among(c, t))
    == G.among.step(p, _u => G.among(c, t)) : Bool}

def among_agrees.arm(_c, _t, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.among_agrees(c, cs):
  match cs:
    case []:
      {==}
    case +h <> +t:
      among_agrees.arm(c, t, Char.is_eq(h, c), Laws.among_agrees(c, t))

# LAW: one step of the ref walk
law hex_all_agrees.arm:
  for t: List<&2, Char>
  for p: Bool
  for ih: {Laws.old.hex.all(t) == G.hex.all(t) : Bool}
  {Bool.and(p, Laws.old.hex.all(t))
    == G.hex.all.step(p, _u => G.hex.all(t)) : Bool}

def hex_all_agrees.arm(_t, p, ih):
  match p:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.hex_all_agrees(cs):
  match cs:
    case []:
      {==}
    case +h <> +t:
      hex_all_agrees.arm(t, G.hex.at(h), Laws.hex_all_agrees(t))

# LAW: one step of the peeled-row search
law peeled_agrees.arm:
  for +h: G.Row
  for t: List<&2, G.Row>
  for p: Bool
  for ih: {Laws.old.peeled(t) == G.peeled(t) : String}
  {Bool.pick(String, p, G.row.rev(h), Laws.old.peeled(t))
    == G.peeled.step(p, G.row.rev(h), _u => G.peeled(t)) : String}

def peeled_agrees.arm(_h, _t, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.peeled_agrees(rs):
  match rs:
    case []:
      {==}
    case +h <> +t:
      peeled_agrees.arm(h, t, G.row.peeled(h), Laws.peeled_agrees(t))

# A ref's length or alphabet is rewritten into `Bool.and`. A table's
# name is rewritten into the keep-or-drop arm. The two root laws
# rewrite a depth comparison into the climb count.

def Laws.is_rev_needs_40(ref, e):
  %e : {Bool.and(_, G.hex.all(String.to_list(ref))) == False{} : Bool}
  {==}

def Laws.is_rev_needs_hex(ref, e0, e1):
  %e0 : {Bool.and(_, G.hex.all(String.to_list(ref))) == False{} : Bool}
  %e1 : {_ == False{} : Bool}
  {==}

def Laws.is_rev_hex40(ref, e0, e1):
  %e0 : {Bool.and(_, G.hex.all(String.to_list(ref))) == True{} : Bool}
  %e1 : {_ == True{} : Bool}
  {==}

def Laws.but_drops(n, ps, rest):
  Equal.cong(Bool, List<&2, T.Sect>,
    b => G.but.put(b, T.Sect{n, ps}, G.but(rest, n)),
    String.eq(n, n), True{}, Eq.string_eq_self(n))

def Laws.but_keeps(n, m, ps, rest, e):
  %e : {G.but.put(_, T.Sect{n, ps}, G.but(rest, m))
    == T.Sect{n, ps} <> G.but(rest, m) : List<&2, T.Sect>}
  {==}

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

# LAW: subtracting a number from itself is nothing
law sub_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}

def sub_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

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

def Laws.root_rel_here(at, root, entry, e):
  Equal.cong(Nat, String,
    n => P.climb(n, P.dir(entry)),
    Nat.sub(G.depth(P.dir(at)), G.depth(root)),
    0n,
    Equal.trans(Nat,
      Nat.sub(G.depth(P.dir(at)), G.depth(root)),
      Nat.sub(G.depth(P.dir(at)), G.depth(P.dir(at))),
      0n,
      Equal.cong(Nat, Nat,
        b => Nat.sub(G.depth(P.dir(at)), b),
        G.depth(root), G.depth(P.dir(at)),
        Equal.sym(Nat, G.depth(P.dir(at)), G.depth(root),
          nat_eq_is(G.depth(P.dir(at)), G.depth(root), e))),
      sub_self(G.depth(P.dir(at)))))

def Laws.sha256_remote_tip():
  {==}

def Laws.sha256_remote_branch():
  {==}

def Laws.root_rel_up(at, root, entry, e):
  Equal.cong(Nat, String,
    n => P.climb(n, P.dir(entry)),
    Nat.sub(G.depth(P.dir(at)), G.depth(root)),
    1n,
    Equal.trans(Nat,
      Nat.sub(G.depth(P.dir(at)), G.depth(root)),
      Nat.sub(1n+G.depth(root), G.depth(root)),
      1n,
      Equal.cong(Nat, Nat,
        a => Nat.sub(a, G.depth(root)),
        G.depth(P.dir(at)), 1n+G.depth(root),
        nat_eq_is(G.depth(P.dir(at)), 1n+G.depth(root), e)),
      sub_succ(G.depth(root))))
