# git: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../lock/lock.bend as L
import ../git/git.bend as G
import ../pkg/path.bend as P
import ../check/eq.bend as Eq
import ../pkg/PROOF.bend as Pk
import ./LAWS.bend as Laws

# The six keys are written out as literals on both sides, so every lookup in
# `L.src_of` decides against a literal and computes: `kind` finds "git", each
# named key finds the pair written for it, and `tag` runs off the end of the
# six into whatever follows. Nothing is left symbolic but the values, and they
# are carried through untouched.
def Laws.origin_read(_url, _rev, _entry, _root, _nar, _ts):
  {==}

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

# The tag choice. `latest.rel` folds the names from the right, and each step
# is one of three picks: pass a name over, take it because nothing after it
# was a release, or weigh it against the greatest release after it. Each pick
# is a match on a computed value, so each is lifted into a parameter with the
# equation that put it there, and the recursive call on the tail arrives as a
# function the arm applies only where the tail is what decides.

# LAW: a release has a name
law release_named:
  for +h: String
  for e: {G.release(h) == True{} : Bool}
  {String.is_empty(h) == False{} : Bool}

def release_named(h, e):
  match h:
    case SNil{}:
      Eq.bit.absurd(&2, {String.is_empty(SNil{}) == False{} : Bool}, e)
    case SCon{_c, _t}:
      {==}

# LAW: a release weighed against another name comes out one of the two
law rel_ne.cmp:
  for +h: String
  for +r: String
  for d: Bool
  for ec: {String.is_empty(r) == False{} : Bool}
  for eb: {G.release(h) == True{} : Bool}
  {String.is_empty(G.latest.cmp(d, h, r)) == False{} : Bool}

def rel_ne.cmp(h, _r, d, ec, eb):
  match d:
    case True{}:
      release_named(h, eb)
    case False{}:
      ec

# LAW: a release taken or weighed leaves a name
law rel_ne.have:
  for +h: String
  for +r: String
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for eb: {G.release(h) == True{} : Bool}
  {String.is_empty(G.latest.have(c, h, r, G.ver.of(h))) == False{} : Bool}

def rel_ne.have(h, r, c, ec, eb):
  match c:
    case True{}:
      release_named(h, eb)
    case False{}:
      rel_ne.cmp(h, r, G.newer(G.ord.ver(G.ver.of(h), G.ver.of(r))), ec, eb)

# LAW: one step of the fold, when some name from here on is a release
law rel_ne.arm:
  for +h: String
  for +t: List<&2, String>
  for b: Bool
  for eb: {G.release(h) == b : Bool}
  for e: {G.has.release.step(b, _u => G.has.release(t)) == True{} : Bool}
  for ih: {G.has.release(t) == True{} : Bool}
    -> {String.is_empty(G.latest.rel(t)) == False{} : Bool}
  {String.is_empty(G.latest.rel.step(b, h, G.latest.rel(t))) == False{} : Bool}

def rel_ne.arm(h, t, b, eb, e, ih):
  match b:
    case False{}:
      ih(e)
    case True{}:
      rel_ne.have(h, G.latest.rel(t), String.is_empty(G.latest.rel(t)), {==}, eb)

# LAW: when some name is a release, the greatest release is a name
law rel_ne:
  for +names: List<&2, String>
  for e: {G.has.release(names) == True{} : Bool}
  {String.is_empty(G.latest.rel(names)) == False{} : Bool}

def rel_ne(names, e):
  match names:
    case []:
      Eq.bit.absurd(&2, {String.is_empty(G.latest.rel([])) == False{} : Bool}, e)
    case +h <> t:
      rel_ne.arm(h, t, G.release(h), {==}, e, x => rel_ne(t, x))

# LAW: a release weighed against another release comes out a release
law rel_is.cmp:
  for +h: String
  for +r: String
  for d: Bool
  for eb: {G.release(h) == True{} : Bool}
  for er: {G.release(r) == True{} : Bool}
  {G.release(G.latest.cmp(d, h, r)) == True{} : Bool}

def rel_is.cmp(_h, _r, d, eb, er):
  match d:
    case True{}:
      eb
    case False{}:
      er

# LAW: a release taken or weighed leaves a release
law rel_is.have:
  for +h: String
  for +r: String
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for eb: {G.release(h) == True{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> {G.release(r) == True{} : Bool}
  {G.release(G.latest.have(c, h, r, G.ver.of(h))) == True{} : Bool}

def rel_is.have(h, r, c, ec, eb, ih):
  match c:
    case True{}:
      eb
    case False{}:
      rel_is.cmp(h, r, G.newer(G.ord.ver(G.ver.of(h), G.ver.of(r))), eb, ih(ec))

# LAW: one step of the fold, when what it answers is a name
law rel_is.arm:
  for +h: String
  for +t: List<&2, String>
  for b: Bool
  for eb: {G.release(h) == b : Bool}
  for e: {String.is_empty(G.latest.rel.step(b, h, G.latest.rel(t))) == False{} : Bool}
  for ih: {String.is_empty(G.latest.rel(t)) == False{} : Bool}
    -> {G.release(G.latest.rel(t)) == True{} : Bool}
  {G.release(G.latest.rel.step(b, h, G.latest.rel(t))) == True{} : Bool}

def rel_is.arm(h, t, b, eb, e, ih):
  match b:
    case False{}:
      ih(e)
    case True{}:
      rel_is.have(h, G.latest.rel(t), String.is_empty(G.latest.rel(t)), {==}, eb, ih)

# LAW: whatever name the fold answers is a release
law rel_is:
  for +names: List<&2, String>
  for e: {String.is_empty(G.latest.rel(names)) == False{} : Bool}
  {G.release(G.latest.rel(names)) == True{} : Bool}

def rel_is(names, e):
  match names:
    case []:
      Eq.bit.absurd2(&2, {G.release(G.latest.rel([])) == True{} : Bool}, e)
    case +h <> t:
      rel_is.arm(h, t, G.release(h), {==}, e, x => rel_is(t, x))

# The choice is rewritten to the arm that takes the release, which the two
# lemmas say is there and is a release.
def Laws.choose_release(names, e):
  +ne = rel_ne(names, e)
  Equal.trans(Bool,
    G.release(G.choose.go(String.is_empty(G.latest.rel(names)),
      G.latest.rel(names), G.latest(names))),
    G.release(G.choose.go(False{}, G.latest.rel(names), G.latest(names))),
    True{},
    Equal.cong(Bool, Bool,
      x => G.release(G.choose.go(x, G.latest.rel(names), G.latest(names))),
      String.is_empty(G.latest.rel(names)), False{}, ne),
    rel_is(names, ne))

# LAW: one step of the fold, when no name from here on is a release
law rel_none.arm:
  for +h: String
  for +t: List<&2, String>
  for b: Bool
  for e: {G.has.release.step(b, _u => G.has.release(t)) == False{} : Bool}
  for ih: {G.has.release(t) == False{} : Bool} -> {G.latest.rel(t) == "" : String}
  {G.latest.rel.step(b, h, G.latest.rel(t)) == "" : String}

def rel_none.arm(h, t, b, e, ih):
  match b:
    case True{}:
      Eq.bit.absurd2(&2, {G.latest.rel.step(True{}, h, G.latest.rel(t)) == "" : String}, e)
    case False{}:
      ih(e)

# LAW: with no release among the names, the fold answers nothing
law rel_none:
  for +names: List<&2, String>
  for e: {G.has.release(names) == False{} : Bool}
  {G.latest.rel(names) == "" : String}

def rel_none(names, e):
  match names:
    case []:
      {==}
    case +h <> t:
      rel_none.arm(h, t, G.release(h), e, x => rel_none(t, x))

def Laws.choose_prerelease(names, e):
  Equal.cong(String, String,
    x => G.choose.go(String.is_empty(x), x, G.latest(names)),
    G.latest.rel(names), "", rel_none(names, e))

# The default branch. A symref row's branch is a literal prefix taken off a
# name that is not empty, so it computes once the name is a char and a rest.
# The other two rows are rewritten to the empty answer that passes them over.

def Laws.branch_of_symref(b, rest, e):
  match b:
    case SNil{}:
      Eq.bit.absurd(&2,
        {G.tip.branch(G.Row{"ref: refs/heads/", "HEAD"} <> rest) == "" : String}, e)
    case SCon{_c, _t}:
      {==}

def Laws.branch_skips_other(rev, _name, rest, e):
  %e : {G.tip.step(String.is_empty(G.tip.branch.pick(_, rev)),
    G.tip.branch.pick(_, rev), _u => G.tip.branch(rest)) == G.tip.branch(rest)
    : String}
  {==}

def Laws.branch_skips_commit(rev, rest, e):
  %e : {G.tip.step(
    String.is_empty(G.tip.strip(Bool.pick(String, _,
      String.drop(rev, String.length("ref: ")), ""), "refs/heads/")),
    G.tip.strip(Bool.pick(String, _,
      String.drop(rev, String.length("ref: ")), ""), "refs/heads/"),
    _u => G.tip.branch(rest)) == G.tip.branch(rest) : String}
  {==}

# The exact pick. A row is compared by its whole name against each of the
# three a ref may have, and each comparison the premises answer is rewritten
# to the arm that passes the row over.

def Laws.exact_skips(rev, name, rs, ref, e0, e1, e2):
  %e0 : {G.or_else(
    G.named.step(_, rev, _u => G.named(rs, "refs/tags/" ++ ref ++ "^{}")),
    G.or_else(
      G.named.step(String.eq(name, "refs/tags/" ++ ref), rev,
        _u => G.named(rs, "refs/tags/" ++ ref)),
      G.named.step(String.eq(name, "refs/heads/" ++ ref), rev,
        _u => G.named(rs, "refs/heads/" ++ ref))))
    == G.exact(rs, ref) : String}
  %e1 : {G.or_else(
    G.named.step(False{}, rev, _u => G.named(rs, "refs/tags/" ++ ref ++ "^{}")),
    G.or_else(
      G.named.step(_, rev, _u => G.named(rs, "refs/tags/" ++ ref)),
      G.named.step(String.eq(name, "refs/heads/" ++ ref), rev,
        _u => G.named(rs, "refs/heads/" ++ ref))))
    == G.exact(rs, ref) : String}
  %e2 : {G.or_else(
    G.named.step(False{}, rev, _u => G.named(rs, "refs/tags/" ++ ref ++ "^{}")),
    G.or_else(
      G.named.step(False{}, rev, _u => G.named(rs, "refs/tags/" ++ ref)),
      G.named.step(_, rev, _u => G.named(rs, "refs/heads/" ++ ref))))
    == G.exact(rs, ref) : String}
  {==}

def Laws.exact_tag_first(rs, ref, e):
  %e : {G.or_else(G.named(rs, "refs/tags/" ++ ref ++ "^{}"),
    Bool.pick(String, _, G.named(rs, "refs/heads/" ++ ref),
      G.named(rs, "refs/tags/" ++ ref)))
    == G.or_else(G.named(rs, "refs/tags/" ++ ref ++ "^{}"),
      G.named(rs, "refs/tags/" ++ ref)) : String}
  {==}

def Laws.exact_branch(rs, ref, e0, e1):
  %e0 : {G.or_else(_, G.or_else(G.named(rs, "refs/tags/" ++ ref),
    G.named(rs, "refs/heads/" ++ ref))) == G.named(rs, "refs/heads/" ++ ref)
    : String}
  %e1 : {G.or_else("", G.or_else(_, G.named(rs, "refs/heads/" ++ ref)))
    == G.named(rs, "refs/heads/" ++ ref) : String}
  {==}

# The version order. `G.ord.ver` answers an `Ord`; read as Base's `Cmp`, each
# layer of it is a lexicographic step over a layer below, the shape
# pkg/PROOF.bend proved consistent for strings: `Pk.tri` says a third
# comparison is one the first two leave room for, and `Pk.cmp.flip` is a
# comparison taken the other way round. Each layer gets a `Cmp` twin that
# computes on constructors, a law that the twin is the layer, and the twin's
# three facts: consistent across three versions, flipped when swapped, and
# EQ against itself. The fold's law needs exactly those: a version the fold
# passed over is below what it kept, and what it kept is below what replaced
# it, so the first is below the last.

# an order read as a comparison
def oc(o: G.Ord) -> Cmp:
  match o:
    case G.Lt{}:
      LT{}
    case G.Eq{}:
      EQ{}
    case G.Gt{}:
      GT{}

# LAW: newer is GT
law newer_gt:
  for o: G.Ord
  {G.newer(o) == Cmp.is_gt(oc(o)) : Bool}

def newer_gt(o):
  match o:
    case G.Lt{}:
      {==}
    case G.Eq{}:
      {==}
    case G.Gt{}:
      {==}

# LAW: a lexicographic step of orders is one of comparisons
law lex_at:
  for o: G.Ord
  for r: G.Ord
  {Pk.cmp.lex(oc(o), oc(r)) == oc(G.ord.nums.at(o, _u => r)) : Cmp}

def lex_at(o, _r):
  match o:
    case G.Lt{}:
      {==}
    case G.Eq{}:
      {==}
    case G.Gt{}:
      {==}

# Numbers.

# LAW: two numbers compared the other way round
law nat.flip:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(b, a) == Pk.cmp.flip(Nat.cmp(a, b)) : Cmp}

def nat.flip(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat.flip(p, q)

# LAW: three numbers compare consistently
law nat.tri:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Pk.tri(Nat.cmp(a, b), Nat.cmp(b, c), Nat.cmp(a, c)) == True{} : Bool}

def nat.tri(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      Pk.tri.lt.free(Nat.cmp(q, r))
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Pk.tri.mid.gt(Nat.cmp(p, q), GT{})
    case 1n+p 1n+q 1n+r:
      nat.tri(p, q, r)

# LAW: a number is EQ to itself
law nat.refl:
  for +a: Nat
  {Nat.cmp(a, a) == EQ{} : Cmp}

def nat.refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      nat.refl(p)

# LAW: the order `ord.nat` builds from a comparison is that comparison
law nat_ord.go:
  for c: Cmp
  {c == oc(G.ord.nat(Cmp.is_eq(c), Cmp.is_lt(c))) : Cmp}

def nat_ord.go(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: and so the order of two numbers is their comparison
law nat_ord:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, b) == oc(G.ord.nat(Nat.is_eq(a, b), Nat.is_lt(a, b))) : Cmp}

def nat_ord(a, b):
  nat_ord.go(Nat.cmp(a, b))

# Dotted numbers. A missing part is a zero, so a list that has run out
# compares as zero against the other's head, and as nothing after it.

# the comparison of two lists of numbers, zero where one has run out
def nums.c(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{+h, t}:
      Pk.cmp.lex(Nat.cmp(0n, h), nums.c([], t))
    case Con{+h, t} Nil{}:
      Pk.cmp.lex(Nat.cmp(h, 0n), nums.c(t, []))
    case Con{+ha, ta} Con{+hb, tb}:
      Pk.cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))

# LAW: one step of padding, with the rest already known
law pad.step:
  for +h: Nat
  for +t: List<&2, Nat>
  for ih: {nums.c([], t) == oc(G.ord.pad(t)) : Cmp}
  {nums.c([], h <> t) == oc(G.ord.pad(h <> t)) : Cmp}

def pad.step(h, _t, ih):
  match h:
    case 0n:
      ih
    case 1n+p:
      {==}

# LAW: a list against nothing is a list against zeros
law pad.c:
  for +t: List<&2, Nat>
  {nums.c([], t) == oc(G.ord.pad(t)) : Cmp}

def pad.c(t):
  match t:
    case []:
      {==}
    case Con{+h, +r}:
      pad.step(h, r, pad.c(r))

# LAW: the same on the other side, one step
law padr.step:
  for +h: Nat
  for +t: List<&2, Nat>
  for ih: {nums.c(t, []) == oc(G.ord.flip(G.ord.pad(t))) : Cmp}
  {nums.c(h <> t, []) == oc(G.ord.flip(G.ord.pad(h <> t))) : Cmp}

def padr.step(h, _t, ih):
  match h:
    case 0n:
      ih
    case 1n+p:
      {==}

# LAW: nothing against a list is zeros against it
law padr.c:
  for +t: List<&2, Nat>
  {nums.c(t, []) == oc(G.ord.flip(G.ord.pad(t))) : Cmp}

def padr.c(t):
  match t:
    case []:
      {==}
    case Con{+h, +r}:
      padr.step(h, r, padr.c(r))

# LAW: the twin is `ord.nums`
law nums.is:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  {nums.c(a, b) == oc(G.ord.nums(a, b)) : Cmp}

def nums.is(a, b):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h, +t}:
      pad.c(h <> t)
    case Con{+h, +t} Nil{}:
      padr.c(h <> t)
    case Con{+ha, +ta} Con{+hb, +tb}:
      %lex_at(G.ord.nat(Nat.is_eq(ha, hb), Nat.is_lt(ha, hb)), G.ord.nums(ta, tb))
        : {nums.c(ha <> ta, hb <> tb) == _ : Cmp}
      %nat_ord(ha, hb) : {Pk.cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))
        == Pk.cmp.lex(_, oc(G.ord.nums(ta, tb))) : Cmp}
      %nums.is(ta, tb) : {Pk.cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))
        == Pk.cmp.lex(Nat.cmp(ha, hb), _) : Cmp}
      {==}

# LAW: dotted numbers compared the other way round
law nums.flip:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  {nums.c(b, a) == Pk.cmp.flip(nums.c(a, b)) : Cmp}

def nums.flip(a, b):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h, +t}:
      %Equal.sym(Cmp, Nat.cmp(h, 0n), Pk.cmp.flip(Nat.cmp(0n, h)), nat.flip(0n, h))
        : {Pk.cmp.lex(_, nums.c(t, [])) == Pk.cmp.flip(
        Pk.cmp.lex(Nat.cmp(0n, h), nums.c([], t))) : Cmp}
      %Equal.sym(Cmp, nums.c(t, []), Pk.cmp.flip(nums.c([], t)), nums.flip([], t))
        : {Pk.cmp.lex(Pk.cmp.flip(Nat.cmp(0n, h)), _)
        == Pk.cmp.flip(Pk.cmp.lex(Nat.cmp(0n, h), nums.c([], t))) : Cmp}
      Pk.lex.flip(Nat.cmp(0n, h), nums.c([], t))
    case Con{+h, +t} Nil{}:
      %Equal.sym(Cmp, Nat.cmp(0n, h), Pk.cmp.flip(Nat.cmp(h, 0n)), nat.flip(h, 0n))
        : {Pk.cmp.lex(_, nums.c([], t)) == Pk.cmp.flip(
        Pk.cmp.lex(Nat.cmp(h, 0n), nums.c(t, []))) : Cmp}
      %Equal.sym(Cmp, nums.c([], t), Pk.cmp.flip(nums.c(t, [])), nums.flip(t, []))
        : {Pk.cmp.lex(Pk.cmp.flip(Nat.cmp(h, 0n)), _)
        == Pk.cmp.flip(Pk.cmp.lex(Nat.cmp(h, 0n), nums.c(t, []))) : Cmp}
      Pk.lex.flip(Nat.cmp(h, 0n), nums.c(t, []))
    case Con{+ha, +ta} Con{+hb, +tb}:
      %Equal.sym(Cmp, Nat.cmp(hb, ha), Pk.cmp.flip(Nat.cmp(ha, hb)), nat.flip(ha, hb))
        : {Pk.cmp.lex(_, nums.c(tb, ta)) == Pk.cmp.flip(
        Pk.cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))) : Cmp}
      %Equal.sym(Cmp, nums.c(tb, ta), Pk.cmp.flip(nums.c(ta, tb)), nums.flip(ta, tb))
        : {Pk.cmp.lex(Pk.cmp.flip(Nat.cmp(ha, hb)), _)
        == Pk.cmp.flip(Pk.cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))) : Cmp}
      Pk.lex.flip(Nat.cmp(ha, hb), nums.c(ta, tb))

# LAW: three lists of dotted numbers compare consistently. A list that has
# run out stands in as a zero and nothing after it, which is why every arm
# is the same lexicographic step.
law nums.tri:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +c: List<&2, Nat>
  {Pk.tri(nums.c(a, b), nums.c(b, c), nums.c(a, c)) == True{} : Bool}

def nums.tri(a, b, c):
  match a b c:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{+hc, +tc}:
      Pk.lex.tri(Nat.cmp(0n, 0n), Nat.cmp(0n, hc), Nat.cmp(0n, hc),
        nums.c([], []), nums.c([], tc), nums.c([], tc),
        nat.tri(0n, 0n, hc), nums.tri([], [], tc))
    case Nil{} Con{+hb, +tb} Nil{}:
      Pk.lex.tri(Nat.cmp(0n, hb), Nat.cmp(hb, 0n), Nat.cmp(0n, 0n),
        nums.c([], tb), nums.c(tb, []), nums.c([], []),
        nat.tri(0n, hb, 0n), nums.tri([], tb, []))
    case Nil{} Con{+hb, +tb} Con{+hc, +tc}:
      Pk.lex.tri(Nat.cmp(0n, hb), Nat.cmp(hb, hc), Nat.cmp(0n, hc),
        nums.c([], tb), nums.c(tb, tc), nums.c([], tc),
        nat.tri(0n, hb, hc), nums.tri([], tb, tc))
    case Con{+ha, +ta} Nil{} Nil{}:
      Pk.lex.tri(Nat.cmp(ha, 0n), Nat.cmp(0n, 0n), Nat.cmp(ha, 0n),
        nums.c(ta, []), nums.c([], []), nums.c(ta, []),
        nat.tri(ha, 0n, 0n), nums.tri(ta, [], []))
    case Con{+ha, +ta} Nil{} Con{+hc, +tc}:
      Pk.lex.tri(Nat.cmp(ha, 0n), Nat.cmp(0n, hc), Nat.cmp(ha, hc),
        nums.c(ta, []), nums.c([], tc), nums.c(ta, tc),
        nat.tri(ha, 0n, hc), nums.tri(ta, [], tc))
    case Con{+ha, +ta} Con{+hb, +tb} Nil{}:
      Pk.lex.tri(Nat.cmp(ha, hb), Nat.cmp(hb, 0n), Nat.cmp(ha, 0n),
        nums.c(ta, tb), nums.c(tb, []), nums.c(ta, []),
        nat.tri(ha, hb, 0n), nums.tri(ta, tb, []))
    case Con{+ha, +ta} Con{+hb, +tb} Con{+hc, +tc}:
      Pk.lex.tri(Nat.cmp(ha, hb), Nat.cmp(hb, hc), Nat.cmp(ha, hc),
        nums.c(ta, tb), nums.c(tb, tc), nums.c(ta, tc),
        nat.tri(ha, hb, hc), nums.tri(ta, tb, tc))

# LAW: dotted numbers are EQ to themselves
law nums.refl:
  for +a: List<&2, Nat>
  {nums.c(a, a) == EQ{} : Cmp}

def nums.refl(a):
  match a:
    case []:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Cmp, Nat.cmp(h, h), EQ{}, nat.refl(h))
        : {Pk.cmp.lex(_, nums.c(t, t)) == EQ{} : Cmp}
      nums.refl(t)

# Pre-release identifiers: a number below a word, numbers by value, words by
# Base's string order.

# the comparison of two identifiers
def id.c(x: G.Id, y: G.Id) -> Cmp:
  match x y:
    case G.IdNum{+n} G.IdNum{+m}:
      Nat.cmp(n, m)
    case G.IdNum{_n} G.IdWord{_s}:
      LT{}
    case G.IdWord{_s} G.IdNum{_n}:
      GT{}
    case G.IdWord{+s} G.IdWord{+t}:
      String.order(s, t)

# LAW: the order `ord.str` builds from a string comparison is its answer
law str_ord.go:
  for r: (String & String) & Cmp
  {String.order.fin(r)
    == oc(G.ord.str(String.eq.fin(r), Cmp.is_le(String.order.fin(r)))) : Cmp}

def str_ord.go(r):
  ((_a, _b), c) = r
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: the twin is `ord.id`
law id.is:
  for +x: G.Id
  for +y: G.Id
  {id.c(x, y) == oc(G.ord.id(x, y)) : Cmp}

def id.is(x, y):
  match x y:
    case G.IdNum{+n} G.IdNum{+m}:
      nat_ord(n, m)
    case G.IdNum{_n} G.IdWord{_s}:
      {==}
    case G.IdWord{_s} G.IdNum{_n}:
      {==}
    case G.IdWord{+s} G.IdWord{+t}:
      str_ord.go(String.cmp(s, t))

# LAW: two identifiers compared the other way round
law id.flip:
  for +x: G.Id
  for +y: G.Id
  {id.c(y, x) == Pk.cmp.flip(id.c(x, y)) : Cmp}

def id.flip(x, y):
  match x y:
    case G.IdNum{+n} G.IdNum{+m}:
      nat.flip(n, m)
    case G.IdNum{_n} G.IdWord{_s}:
      {==}
    case G.IdWord{_s} G.IdNum{_n}:
      {==}
    case G.IdWord{+s} G.IdWord{+t}:
      Pk.str.flip(s, t)

# LAW: three identifiers compare consistently
law id.tri:
  for +x: G.Id
  for +y: G.Id
  for +z: G.Id
  {Pk.tri(id.c(x, y), id.c(y, z), id.c(x, z)) == True{} : Bool}

def id.tri(x, y, z):
  match x y z:
    case G.IdNum{+a} G.IdNum{+b} G.IdNum{+c}:
      nat.tri(a, b, c)
    case G.IdNum{+a} G.IdNum{+b} G.IdWord{_c}:
      Pk.tri.free.lt(Nat.cmp(a, b))
    case G.IdNum{_a} G.IdWord{_b} G.IdNum{_c}:
      {==}
    case G.IdNum{_a} G.IdWord{+b} G.IdWord{+c}:
      Pk.tri.lt.free(String.order(b, c))
    case G.IdWord{_a} G.IdNum{_b} G.IdNum{_c}:
      {==}
    case G.IdWord{_a} G.IdNum{_b} G.IdWord{_c}:
      {==}
    case G.IdWord{+a} G.IdWord{+b} G.IdNum{_c}:
      Pk.tri.mid.gt(String.order(a, b), GT{})
    case G.IdWord{+a} G.IdWord{+b} G.IdWord{+c}:
      Pk.str.tri(a, b, c)

# LAW: an identifier is EQ to itself
law id.refl:
  for +x: G.Id
  {id.c(x, x) == EQ{} : Cmp}

def id.refl(x):
  match x:
    case G.IdNum{+n}:
      nat.refl(n)
    case G.IdWord{+s}:
      Equal.cong((String & String) & Cmp, Cmp, r => String.order.fin(r),
        String.cmp(s, s), ((s, s), EQ{}), Eq.string_cmp_self(s))

# A pre-release's identifiers, one at a time; a list that runs out first is
# the lesser.

# the comparison of two lists of identifiers
def ids.c(xs: List<&2, G.Id>, ys: List<&2, G.Id>) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{_h, _t}:
      LT{}
    case Con{_h, _t} Nil{}:
      GT{}
    case Con{+ha, ta} Con{+hb, tb}:
      Pk.cmp.lex(id.c(ha, hb), ids.c(ta, tb))

# LAW: the twin is `ord.ids`
law ids.is:
  for +xs: List<&2, G.Id>
  for +ys: List<&2, G.Id>
  {ids.c(xs, ys) == oc(G.ord.ids(xs, ys)) : Cmp}

def ids.is(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      %lex_at(G.ord.id(ha, hb), G.ord.ids(ta, tb))
        : {ids.c(ha <> ta, hb <> tb) == _ : Cmp}
      %id.is(ha, hb) : {Pk.cmp.lex(id.c(ha, hb), ids.c(ta, tb))
        == Pk.cmp.lex(_, oc(G.ord.ids(ta, tb))) : Cmp}
      %ids.is(ta, tb) : {Pk.cmp.lex(id.c(ha, hb), ids.c(ta, tb))
        == Pk.cmp.lex(id.c(ha, hb), _) : Cmp}
      {==}

# LAW: identifier lists compared the other way round
law ids.flip:
  for +xs: List<&2, G.Id>
  for +ys: List<&2, G.Id>
  {ids.c(ys, xs) == Pk.cmp.flip(ids.c(xs, ys)) : Cmp}

def ids.flip(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      %Equal.sym(Cmp, id.c(hb, ha), Pk.cmp.flip(id.c(ha, hb)), id.flip(ha, hb))
        : {Pk.cmp.lex(_, ids.c(tb, ta)) == Pk.cmp.flip(
          Pk.cmp.lex(id.c(ha, hb), ids.c(ta, tb))) : Cmp}
      %Equal.sym(Cmp, ids.c(tb, ta), Pk.cmp.flip(ids.c(ta, tb)), ids.flip(ta, tb))
        : {Pk.cmp.lex(Pk.cmp.flip(id.c(ha, hb)), _) == Pk.cmp.flip(
          Pk.cmp.lex(id.c(ha, hb), ids.c(ta, tb))) : Cmp}
      Pk.lex.flip(id.c(ha, hb), ids.c(ta, tb))

# LAW: three identifier lists compare consistently
law ids.tri:
  for +xs: List<&2, G.Id>
  for +ys: List<&2, G.Id>
  for +zs: List<&2, G.Id>
  {Pk.tri(ids.c(xs, ys), ids.c(ys, zs), ids.c(xs, zs)) == True{} : Bool}

def ids.tri(xs, ys, zs):
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{_hc, _tc}:
      {==}
    case Nil{} Con{_hb, _tb} Nil{}:
      {==}
    case Nil{} Con{+hb, +tb} Con{+hc, +tc}:
      Pk.tri.lt.free(ids.c(hb <> tb, hc <> tc))
    case Con{_ha, _ta} Nil{} Nil{}:
      {==}
    case Con{_ha, _ta} Nil{} Con{_hc, _tc}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb} Nil{}:
      Pk.tri.mid.gt(ids.c(ha <> ta, hb <> tb), GT{})
    case Con{+ha, +ta} Con{+hb, +tb} Con{+hc, +tc}:
      Pk.lex.tri(id.c(ha, hb), id.c(hb, hc), id.c(ha, hc),
        ids.c(ta, tb), ids.c(tb, tc), ids.c(ta, tc),
        id.tri(ha, hb, hc), ids.tri(ta, tb, tc))

# LAW: an identifier list is EQ to itself
law ids.refl:
  for +xs: List<&2, G.Id>
  {ids.c(xs, xs) == EQ{} : Cmp}

def ids.refl(xs):
  match xs:
    case []:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Cmp, id.c(h, h), EQ{}, id.refl(h))
        : {Pk.cmp.lex(_, ids.c(t, t)) == EQ{} : Cmp}
      ids.refl(t)

# A release, with no identifiers, is above every pre-release of it.

# the comparison of two pre-releases, the empty one a release
def rel.c(p: List<&2, G.Id>, q: List<&2, G.Id>) -> Cmp:
  match p q:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{_h, _t}:
      GT{}
    case Con{_h, _t} Nil{}:
      LT{}
    case Con{+ha, +ta} Con{+hb, +tb}:
      ids.c(ha <> ta, hb <> tb)

# LAW: the twin is `ord.rel`
law rel.is:
  for +p: List<&2, G.Id>
  for +q: List<&2, G.Id>
  {rel.c(p, q) == oc(G.ord.rel(p, q)) : Cmp}

def rel.is(p, q):
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      ids.is(ha <> ta, hb <> tb)

# LAW: pre-releases compared the other way round
law rel.flip:
  for +p: List<&2, G.Id>
  for +q: List<&2, G.Id>
  {rel.c(q, p) == Pk.cmp.flip(rel.c(p, q)) : Cmp}

def rel.flip(p, q):
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      ids.flip(ha <> ta, hb <> tb)

# LAW: three pre-releases compare consistently
law rel.tri:
  for +p: List<&2, G.Id>
  for +q: List<&2, G.Id>
  for +r: List<&2, G.Id>
  {Pk.tri(rel.c(p, q), rel.c(q, r), rel.c(p, r)) == True{} : Bool}

def rel.tri(p, q, r):
  match p q r:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{_hc, _tc}:
      {==}
    case Nil{} Con{_hb, _tb} Nil{}:
      {==}
    case Nil{} Con{_hb, _tb} Con{_hc, _tc}:
      {==}
    case Con{_ha, _ta} Nil{} Nil{}:
      {==}
    case Con{_ha, _ta} Nil{} Con{_hc, _tc}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb} Nil{}:
      Pk.tri.free.lt(ids.c(ha <> ta, hb <> tb))
    case Con{+ha, +ta} Con{+hb, +tb} Con{+hc, +tc}:
      ids.tri(ha <> ta, hb <> tb, hc <> tc)

# LAW: a pre-release is EQ to itself
law rel.refl:
  for +p: List<&2, G.Id>
  {rel.c(p, p) == EQ{} : Cmp}

def rel.refl(p):
  match p:
    case []:
      {==}
    case Con{+h, +t}:
      ids.refl(h <> t)

# A version: its numbers, and its pre-release where they tie.

# the comparison of two versions, each given as its numbers and pre-release
def ver.c(na: List<&2, Nat>, pa: List<&2, G.Id>, nb: List<&2, Nat>, pb: List<&2, G.Id>) -> Cmp:
  Pk.cmp.lex(nums.c(na, nb), rel.c(pa, pb))

# LAW: the twin is `ord.ver` of two semver-ish versions
law ver.is:
  for +na: List<&2, Nat>
  for +pa: List<&2, G.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, G.Id>
  {ver.c(na, pa, nb, pb) == oc(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb})) : Cmp}

def ver.is(na, pa, nb, pb):
  %lex_at(G.ord.nums(na, nb), G.ord.rel(pa, pb))
    : {ver.c(na, pa, nb, pb) == _ : Cmp}
  %nums.is(na, nb) : {Pk.cmp.lex(nums.c(na, nb), rel.c(pa, pb))
    == Pk.cmp.lex(_, oc(G.ord.rel(pa, pb))) : Cmp}
  %rel.is(pa, pb) : {Pk.cmp.lex(nums.c(na, nb), rel.c(pa, pb))
    == Pk.cmp.lex(nums.c(na, nb), _) : Cmp}
  {==}

# LAW: versions compared the other way round
law ver.flip:
  for +na: List<&2, Nat>
  for +pa: List<&2, G.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, G.Id>
  {ver.c(nb, pb, na, pa) == Pk.cmp.flip(ver.c(na, pa, nb, pb)) : Cmp}

def ver.flip(na, pa, nb, pb):
  %Equal.sym(Cmp, nums.c(nb, na), Pk.cmp.flip(nums.c(na, nb)), nums.flip(na, nb))
    : {Pk.cmp.lex(_, rel.c(pb, pa))
      == Pk.cmp.flip(Pk.cmp.lex(nums.c(na, nb), rel.c(pa, pb))) : Cmp}
  %Equal.sym(Cmp, rel.c(pb, pa), Pk.cmp.flip(rel.c(pa, pb)), rel.flip(pa, pb))
    : {Pk.cmp.lex(Pk.cmp.flip(nums.c(na, nb)), _)
      == Pk.cmp.flip(Pk.cmp.lex(nums.c(na, nb), rel.c(pa, pb))) : Cmp}
  Pk.lex.flip(nums.c(na, nb), rel.c(pa, pb))

# LAW: three versions compare consistently
law ver.tri:
  for +na: List<&2, Nat>
  for +pa: List<&2, G.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, G.Id>
  for +nc: List<&2, Nat>
  for +pc: List<&2, G.Id>
  {Pk.tri(ver.c(na, pa, nb, pb), ver.c(nb, pb, nc, pc), ver.c(na, pa, nc, pc))
    == True{} : Bool}

def ver.tri(na, pa, nb, pb, nc, pc):
  Pk.lex.tri(nums.c(na, nb), nums.c(nb, nc), nums.c(na, nc),
    rel.c(pa, pb), rel.c(pb, pc), rel.c(pa, pc),
    nums.tri(na, nb, nc), rel.tri(pa, pb, pc))

# LAW: a version is EQ to itself
law ver.refl:
  for +na: List<&2, Nat>
  for +pa: List<&2, G.Id>
  {ver.c(na, pa, na, pa) == EQ{} : Cmp}

def ver.refl(na, pa):
  %Equal.sym(Cmp, nums.c(na, na), EQ{}, nums.refl(na))
    : {Pk.cmp.lex(_, rel.c(pa, pa)) == EQ{} : Cmp}
  rel.refl(pa)

# From comparisons back to `newer`, which is what the folds ask.

# LAW: one semver-ish version newer than another is the twin answering GT
law newer_ver:
  for +na: List<&2, Nat>
  for +pa: List<&2, G.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, G.Id>
  {G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb}))
    == Cmp.is_gt(ver.c(na, pa, nb, pb)) : Bool}

def newer_ver(na, pa, nb, pb):
  %Equal.sym(Cmp, ver.c(na, pa, nb, pb),
    oc(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb})), ver.is(na, pa, nb, pb))
    : {G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb})) == Cmp.is_gt(_) : Bool}
  newer_gt(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb}))

# LAW: what is not above c, where b is above c, is not above b. With the
# middle taken the other way round, this is `Pk.tri` read at the one row that
# matters.
law below.go:
  for u: Cmp
  for y: Cmp
  for w: Cmp
  for t: {Pk.tri(u, Pk.cmp.flip(y), w) == True{} : Bool}
  for eu: {Cmp.is_gt(u) == False{} : Bool}
  for ey: {Cmp.is_gt(y) == True{} : Bool}
  {Cmp.is_gt(w) == False{} : Bool}

def below.go(u, y, w, t, eu, ey):
  match u y:
    case LT{} GT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(EQ{}) == False{} : Bool}, t)
        case GT{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(GT{}) == False{} : Bool}, t)
    case EQ{} GT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(EQ{}) == False{} : Bool}, t)
        case GT{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(GT{}) == False{} : Bool}, t)
    case LT{} LT{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case LT{} EQ{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case EQ{} LT{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case EQ{} EQ{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case GT{} _:
      Eq.bit.absurd2(&2, {Cmp.is_gt(w) == False{} : Bool}, eu)

# LAW: the key lemma. A version not newer than c, where b is newer than c, is
# not newer than b: the order is transitive, so a fold that replaces c by b
# keeps every version it passed below what it holds.
law ver.below:
  for +na: List<&2, Nat>
  for +pa: List<&2, G.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, G.Id>
  for +nc: List<&2, Nat>
  for +pc: List<&2, G.Id>
  for ea: {G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nc, pc})) == False{} : Bool}
  for eb: {G.newer(G.ord.ver(G.Yes{nb, pb}, G.Yes{nc, pc})) == True{} : Bool}
  {G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb})) == False{} : Bool}

def ver.below(na, pa, nb, pb, nc, pc, ea, eb):
  %Equal.sym(Bool, G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nb, pb})),
    Cmp.is_gt(ver.c(na, pa, nb, pb)), newer_ver(na, pa, nb, pb))
    : {_ == False{} : Bool}
  below.go(ver.c(na, pa, nc, pc), ver.c(nb, pb, nc, pc), ver.c(na, pa, nb, pb),
    Equal.trans(Bool,
      Pk.tri(ver.c(na, pa, nc, pc), Pk.cmp.flip(ver.c(nb, pb, nc, pc)),
        ver.c(na, pa, nb, pb)),
      Pk.tri(ver.c(na, pa, nc, pc), ver.c(nc, pc, nb, pb),
        ver.c(na, pa, nb, pb)),
      True{},
      Equal.cong(Cmp, Bool,
        x => Pk.tri(ver.c(na, pa, nc, pc), x, ver.c(na, pa, nb, pb)),
        Pk.cmp.flip(ver.c(nb, pb, nc, pc)), ver.c(nc, pc, nb, pb),
        Equal.sym(Cmp, ver.c(nc, pc, nb, pb), Pk.cmp.flip(ver.c(nb, pb, nc, pc)),
          ver.flip(nb, pb, nc, pc))),
      ver.tri(na, pa, nc, pc, nb, pb)),
    Equal.trans(Bool, Cmp.is_gt(ver.c(na, pa, nc, pc)),
      G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nc, pc})), False{},
      Equal.sym(Bool, G.newer(G.ord.ver(G.Yes{na, pa}, G.Yes{nc, pc})),
        Cmp.is_gt(ver.c(na, pa, nc, pc)), newer_ver(na, pa, nc, pc)),
      ea),
    Equal.trans(Bool, Cmp.is_gt(ver.c(nb, pb, nc, pc)),
      G.newer(G.ord.ver(G.Yes{nb, pb}, G.Yes{nc, pc})), True{},
      Equal.sym(Bool, G.newer(G.ord.ver(G.Yes{nb, pb}, G.Yes{nc, pc})),
        Cmp.is_gt(ver.c(nb, pb, nc, pc)), newer_ver(nb, pb, nc, pc)),
      eb))

# LAW: the same over any three versions. A name that is not semver-ish is
# newer than nothing and nothing is newer than it, so only three semver-ish
# versions have anything to say.
law top.go:
  for +vn: G.Ver
  for +vh: G.Ver
  for +vr: G.Ver
  for ea: {G.newer(G.ord.ver(vn, vr)) == False{} : Bool}
  for eb: {G.newer(G.ord.ver(vh, vr)) == True{} : Bool}
  {G.newer(G.ord.ver(vn, vh)) == False{} : Bool}

def top.go(vn, vh, vr, ea, eb):
  match vn vh vr:
    case G.No{} _ _:
      {==}
    case G.Yes{_na, _pa} G.No{} _:
      Eq.bit.absurd(&2, {G.newer(G.ord.ver(G.Yes{_na, _pa}, G.No{})) == False{}
        : Bool}, eb)
    case G.Yes{_na, _pa} G.Yes{_nb, _pb} G.No{}:
      Eq.bit.absurd(&2, {G.newer(G.ord.ver(G.Yes{_na, _pa}, G.Yes{_nb, _pb}))
        == False{} : Bool}, eb)
    case G.Yes{+na, +pa} G.Yes{+nb, +pb} G.Yes{+nc, +pc}:
      ver.below(na, pa, nb, pb, nc, pc, ea, eb)

# LAW: no version is newer than itself
law self.go:
  for +v: G.Ver
  {G.newer(G.ord.ver(v, v)) == False{} : Bool}

def self.go(v):
  match v:
    case G.No{}:
      {==}
    case G.Yes{+n, +p}:
      %Equal.sym(Bool, G.newer(G.ord.ver(G.Yes{n, p}, G.Yes{n, p})),
        Cmp.is_gt(ver.c(n, p, n, p)), newer_ver(n, p, n, p))
        : {_ == False{} : Bool}
      %Equal.sym(Cmp, ver.c(n, p, n, p), EQ{}, ver.refl(n, p))
        : {Cmp.is_gt(_) == False{} : Bool}
      {==}

# The folds. Both run from the right and hold the greatest name so far; a
# name is weighed against it by `latest.have`, which the release fold shares.
# A tag `n` sits somewhere in `xs ++ [n] ++ ys`: the folds meet `ys` first,
# then `n`, which the fold takes or passes over for something not below it,
# then each of `xs`, which only ever replaces what it holds with something
# newer. `ver.below` carries `n` across each replacement.

# a version clash: nothing is both a tag and not one
def ver.emp(v: G.Ver) -> Type:
  match v:
    case G.No{}:
      Unit
    case G.Yes{_ns, _ps}:
      Empty

def ver.clash(
  -ns: List<&2, Nat>,
  -ps: List<&2, G.Id>,
  eq: {G.No{} == G.Yes{ns, ps} : G.Ver}
) -> Empty:
  %eq : ver.emp(_)
  Unit{}

# LAW: a semver-ish tag has a name
law named:
  for +n: String
  for ns: List<&2, Nat>
  for ps: List<&2, G.Id>
  for ev: {G.ver.of(n) == G.Yes{ns, ps} : G.Ver}
  {String.is_empty(n) == False{} : Bool}

def named(n, ns, ps, ev):
  match n:
    case SNil{}:
      Eq.bit.gone(&2, {String.is_empty(SNil{}) == False{} : Bool},
        ver.clash(ns, ps, ev))
    case SCon{_c, _t}:
      {==}

# LAW: a name weighed against a name leaves a name
law ne.cmp:
  for +n: String
  for +r: String
  for d: Bool
  for ec: {String.is_empty(r) == False{} : Bool}
  for nn: {String.is_empty(n) == False{} : Bool}
  {String.is_empty(G.latest.cmp(d, n, r)) == False{} : Bool}

def ne.cmp(_n, _r, d, ec, nn):
  match d:
    case True{}:
      nn
    case False{}:
      ec

# LAW: a name taken or weighed leaves a name
law ne.have:
  for +n: String
  for +r: String
  for +v: G.Ver
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for nn: {String.is_empty(n) == False{} : Bool}
  {String.is_empty(G.latest.have(c, n, r, v)) == False{} : Bool}

def ne.have(n, r, v, c, ec, nn):
  match c:
    case True{}:
      nn
    case False{}:
      ne.cmp(n, r, G.newer(G.ord.ver(v, G.ver.of(r))), ec, nn)

# LAW: the fold's step at `n` leaves a name
law ne.head:
  for +n: String
  for +r: String
  for +v: G.Ver
  for ev: {G.ver.of(n) == v : G.Ver}
  for ns: List<&2, Nat>
  for ps: List<&2, G.Id>
  for evn: {G.ver.of(n) == G.Yes{ns, ps} : G.Ver}
  {String.is_empty(G.latest.step(v, n, r)) == False{} : Bool}

def ne.head(n, r, v, ev, ns, ps, evn):
  match v:
    case G.No{}:
      Eq.bit.gone(&2, {String.is_empty(G.latest.step(G.No{}, n, r)) == False{}
        : Bool}, ver.clash(ns, ps,
          Equal.trans(G.Ver, G.No{}, G.ver.of(n), G.Yes{ns, ps},
            Equal.sym(G.Ver, G.ver.of(n), G.No{}, ev), evn)))
    case G.Yes{+a, +b}:
      ne.have(n, r, G.Yes{a, b}, String.is_empty(r), {==}, named(n, a, b, ev))

# LAW: a step past `n` keeps a name
law ne.tail:
  for +h: String
  for +r: String
  for +v: G.Ver
  for ev: {G.ver.of(h) == v : G.Ver}
  for ih: {String.is_empty(r) == False{} : Bool}
  {String.is_empty(G.latest.step(v, h, r)) == False{} : Bool}

def ne.tail(h, r, v, ev, ih):
  match v:
    case G.No{}:
      ih
    case G.Yes{+a, +b}:
      ne.have(h, r, G.Yes{a, b}, String.is_empty(r), {==}, named(h, a, b, ev))

# LAW: with a semver-ish tag in the list, `latest` answers a name
law latest.ne:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for ns: List<&2, Nat>
  for ps: List<&2, G.Id>
  for ev: {G.ver.of(n) == G.Yes{ns, ps} : G.Ver}
  {String.is_empty(G.latest(List.append(&2, String, xs, n <> ys))) == False{}
    : Bool}

def latest.ne(xs, n, ys, ns, ps, ev):
  match xs:
    case []:
      ne.head(n, G.latest(ys), G.ver.of(n), {==}, ns, ps, ev)
    case +h <> t:
      ne.tail(h, G.latest(List.append(&2, String, t, n <> ys)), G.ver.of(h), {==},
        latest.ne(t, n, ys, ns, ps, ev))

# LAW: weighing `n` against what the fold holds keeps nothing newer than `n`
law head.cmp:
  for +n: String
  for +r: String
  for +vn: G.Ver
  for ev: {G.ver.of(n) == vn : G.Ver}
  for d: Bool
  for ed: {G.newer(G.ord.ver(vn, G.ver.of(r))) == d : Bool}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.cmp(d, n, r)))) == False{}
    : Bool}

def head.cmp(n, r, vn, ev, d, ed):
  match d:
    case True{}:
      self.go(G.ver.of(n))
    case False{}:
      %Equal.sym(G.Ver, G.ver.of(n), vn, ev)
        : {G.newer(G.ord.ver(_, G.ver.of(r))) == False{} : Bool}
      ed

# LAW: and so does taking `n` when the fold holds nothing
law head.have:
  for +n: String
  for +r: String
  for +vn: G.Ver
  for ev: {G.ver.of(n) == vn : G.Ver}
  for c: Bool
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.have(c, n, r, vn))))
    == False{} : Bool}

def head.have(n, r, vn, ev, c):
  match c:
    case True{}:
      self.go(G.ver.of(n))
    case False{}:
      head.cmp(n, r, vn, ev, G.newer(G.ord.ver(vn, G.ver.of(r))), {==})

# LAW: the fold's step at `n` holds nothing newer than `n`
law head.step:
  for +n: String
  for +r: String
  for +v: G.Ver
  for ev: {G.ver.of(n) == v : G.Ver}
  for ns: List<&2, Nat>
  for ps: List<&2, G.Id>
  for evn: {G.ver.of(n) == G.Yes{ns, ps} : G.Ver}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.step(v, n, r)))) == False{}
    : Bool}

def head.step(n, r, v, ev, ns, ps, evn):
  match v:
    case G.No{}:
      Eq.bit.gone(&2, {G.newer(G.ord.ver(G.ver.of(n),
        G.ver.of(G.latest.step(G.No{}, n, r)))) == False{} : Bool},
        ver.clash(ns, ps,
          Equal.trans(G.Ver, G.No{}, G.ver.of(n), G.Yes{ns, ps},
            Equal.sym(G.Ver, G.ver.of(n), G.No{}, ev), evn)))
    case G.Yes{+a, +b}:
      head.have(n, r, G.Yes{a, b}, ev, String.is_empty(r))

# LAW: a name after `n` that replaces what the fold holds is newer than it,
# so `n` stays below
law have.cmp:
  for +h: String
  for +r: String
  for +n: String
  for +vh: G.Ver
  for evh: {G.ver.of(h) == vh : G.Ver}
  for d: Bool
  for ed: {G.newer(G.ord.ver(vh, G.ver.of(r))) == d : Bool}
  for ih: {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(r))) == False{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.cmp(d, h, r)))) == False{}
    : Bool}

def have.cmp(h, r, n, vh, evh, d, ed, ih):
  match d:
    case False{}:
      ih
    case True{}:
      %Equal.sym(G.Ver, G.ver.of(h), vh, evh)
        : {G.newer(G.ord.ver(G.ver.of(n), _)) == False{} : Bool}
      top.go(G.ver.of(n), vh, G.ver.of(r), ih, ed)

# LAW: weighing a name after `n` against a name the fold holds keeps `n` below
law have.top:
  for +h: String
  for +r: String
  for +n: String
  for +vh: G.Ver
  for evh: {G.ver.of(h) == vh : G.Ver}
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for ne: {String.is_empty(r) == False{} : Bool}
  for ih: {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(r))) == False{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.have(c, h, r, vh))))
    == False{} : Bool}

def have.top(h, r, n, vh, evh, c, ec, ne, ih):
  match c:
    case True{}:
      Eq.bit.absurd2(&2, {G.newer(G.ord.ver(G.ver.of(n),
        G.ver.of(G.latest.have(True{}, h, r, vh)))) == False{} : Bool},
        Equal.trans(Bool, True{}, String.is_empty(r), False{},
          Equal.sym(Bool, String.is_empty(r), True{}, ec), ne))
    case False{}:
      have.cmp(h, r, n, vh, evh, G.newer(G.ord.ver(vh, G.ver.of(r))), {==}, ih)

# LAW: a step of `latest` past `n` keeps `n` below
law tail.step:
  for +h: String
  for +r: String
  for +n: String
  for +v: G.Ver
  for ev: {G.ver.of(h) == v : G.Ver}
  for ne: {String.is_empty(r) == False{} : Bool}
  for ih: {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(r))) == False{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.step(v, h, r)))) == False{}
    : Bool}

def tail.step(h, r, n, v, ev, ne, ih):
  match v:
    case G.No{}:
      ih
    case G.Yes{+a, +b}:
      have.top(h, r, n, G.Yes{a, b}, ev, String.is_empty(r), {==}, ne, ih)

def Laws.latest_greatest(xs, n, ys, ns, ps, ev):
  match xs:
    case []:
      head.step(n, G.latest(ys), G.ver.of(n), {==}, ns, ps, ev)
    case +h <> t:
      tail.step(h, G.latest(List.append(&2, String, t, n <> ys)), n, G.ver.of(h),
        {==}, latest.ne(t, n, ys, ns, ps, ev),
        Laws.latest_greatest(t, n, ys, ns, ps, ev))

# LAW: a release in the list makes the list have one
law has.hd:
  for +n: String
  for +ys: List<&2, String>
  for b: Bool
  for eb: {G.release(n) == b : Bool}
  for er: {G.release(n) == True{} : Bool}
  {G.has.release.step(b, _u => G.has.release(ys)) == True{} : Bool}

def has.hd(n, ys, b, eb, er):
  match b:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {G.has.release.step(False{}, _u => G.has.release(ys))
        == True{} : Bool},
        Equal.trans(Bool, False{}, G.release(n), True{},
          Equal.sym(Bool, G.release(n), False{}, eb), er))

# LAW: and a name in front of it does not take that away
law has.tl:
  for +t: List<&2, String>
  for b: Bool
  for ih: {G.has.release(t) == True{} : Bool}
  {G.has.release.step(b, _u => G.has.release(t)) == True{} : Bool}

def has.tl(_t, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: a list with a release in it has one
law has.mem:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for er: {G.release(n) == True{} : Bool}
  {G.has.release(List.append(&2, String, xs, n <> ys)) == True{} : Bool}

def has.mem(xs, n, ys, er):
  match xs:
    case []:
      has.hd(n, ys, G.release(n), {==}, er)
    case +h <> t:
      has.tl(List.append(&2, String, t, n <> ys), G.release(h),
        has.mem(t, n, ys, er))

# LAW: the release fold's step at `n` holds nothing newer than `n`
law relh.step:
  for +n: String
  for +r: String
  for b: Bool
  for eb: {G.release(n) == b : Bool}
  for er: {G.release(n) == True{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.rel.step(b, n, r))))
    == False{} : Bool}

def relh.step(n, r, b, eb, er):
  match b:
    case True{}:
      head.have(n, r, G.ver.of(n), {==}, String.is_empty(r))
    case False{}:
      Eq.bit.absurd(&2, {G.newer(G.ord.ver(G.ver.of(n),
        G.ver.of(G.latest.rel.step(False{}, n, r)))) == False{} : Bool},
        Equal.trans(Bool, False{}, G.release(n), True{},
          Equal.sym(Bool, G.release(n), False{}, eb), er))

# LAW: a step of the release fold past `n` keeps `n` below
law relt.step:
  for +h: String
  for +r: String
  for +n: String
  for b: Bool
  for ne: {String.is_empty(r) == False{} : Bool}
  for ih: {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(r))) == False{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.latest.rel.step(b, h, r))))
    == False{} : Bool}

def relt.step(h, r, n, b, ne, ih):
  match b:
    case False{}:
      ih
    case True{}:
      have.top(h, r, n, G.ver.of(h), {==}, String.is_empty(r), {==}, ne, ih)

def Laws.latest_rel_greatest(xs, n, ys, e):
  match xs:
    case []:
      relh.step(n, G.latest.rel(ys), G.release(n), {==}, e)
    case +h <> t:
      relt.step(h, G.latest.rel(List.append(&2, String, t, n <> ys)), n,
        G.release(h),
        rel_ne(List.append(&2, String, t, n <> ys), has.mem(t, n, ys, e)),
        Laws.latest_rel_greatest(t, n, ys, e))

# The choice is rewritten to the fold it takes: the release fold when the
# list has a release, and `latest` when it has none.
def Laws.choose_greatest_release(xs, n, ys, e):
  %Equal.sym(Bool,
    String.is_empty(G.latest.rel(List.append(&2, String, xs, n <> ys))), False{},
    rel_ne(List.append(&2, String, xs, n <> ys), has.mem(xs, n, ys, e)))
    : {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(G.choose.go(_,
      G.latest.rel(List.append(&2, String, xs, n <> ys)),
      G.latest(List.append(&2, String, xs, n <> ys)))))) == False{} : Bool}
  Laws.latest_rel_greatest(xs, n, ys, e)

def Laws.choose_greatest_prerelease(xs, n, ys, ns, ps, ev, e):
  %Equal.sym(String, G.choose(List.append(&2, String, xs, n <> ys)),
    G.latest(List.append(&2, String, xs, n <> ys)),
    Laws.choose_prerelease(List.append(&2, String, xs, n <> ys), e))
    : {G.newer(G.ord.ver(G.ver.of(n), G.ver.of(_))) == False{} : Bool}
  Laws.latest_greatest(xs, n, ys, ns, ps, ev)

# The chosen tag is one of the tags. `Mem(x, names)` is the shape
# `choose_is_a_tag` asks for: `names` split around `x`. Each fold answers the
# name in front, which splits there, or what it held from the rest, which
# splits one further along.

# `x` sits in `names`
def Mem(x: String, names: List<&2, String>) -> Type:
  &xs: List<&2, String> -> &ys: List<&2, String> ->
    {List.append(&2, String, xs, x <> ys) == names : List<&2, String>}

# LAW: the name in front is in the list
law mem.here:
  for +h: String
  for +t: List<&2, String>
  Mem(h, h <> t)

def mem.here(_h, t):
  ([], (t, {==}))

# LAW: a name in the rest is in the list
law mem.there:
  for +h: String
  for +t: List<&2, String>
  for +x: String
  for ih: Mem(x, t)
  Mem(x, h <> t)

def mem.there(h, t, x, ih):
  (xs, (ys, p)) = ih
  (h <> xs, (ys, Equal.cong(List<&2, String>, List<&2, String>, l => h <> l,
    List.append(&2, String, xs, x <> ys), t, p)))

# LAW: a name weighed against what the fold holds leaves one of the two
law mem.cmp:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for d: Bool
  for ec: {String.is_empty(r) == False{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(G.latest.cmp(d, h, r), h <> t)

def mem.cmp(h, t, r, d, ec, ih):
  match d:
    case True{}:
      mem.here(h, t)
    case False{}:
      mem.there(h, t, r, ih(ec))

# LAW: and so does taking it when the fold holds nothing
law mem.have:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for +v: G.Ver
  for c: Bool
  for ec: {String.is_empty(r) == c : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(G.latest.have(c, h, r, v), h <> t)

def mem.have(h, t, r, v, c, ec, ih):
  match c:
    case True{}:
      mem.here(h, t)
    case False{}:
      mem.cmp(h, t, r, G.newer(G.ord.ver(v, G.ver.of(r))), ec, ih)

# LAW: one step of `latest` answers a name in the list, when it answers one
law mem.step:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for +v: G.Ver
  for e: {String.is_empty(G.latest.step(v, h, r)) == False{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(G.latest.step(v, h, r), h <> t)

def mem.step(h, t, r, v, e, ih):
  match v:
    case G.No{}:
      mem.there(h, t, r, ih(e))
    case G.Yes{+a, +b}:
      mem.have(h, t, r, G.Yes{a, b}, String.is_empty(r), {==}, ih)

# LAW: `latest` answers a name in the list, when it answers one
law latest.mem:
  for +names: List<&2, String>
  for e: {String.is_empty(G.latest(names)) == False{} : Bool}
  Mem(G.latest(names), names)

def latest.mem(names, e):
  match names:
    case []:
      Eq.bit.absurd2(&1, Mem(G.latest([]), []), e)
    case +h <> t:
      mem.step(h, t, G.latest(t), G.ver.of(h), e, x => latest.mem(t, x))

# LAW: one step of the release fold answers a name in the list
law mem.rel.step:
  for +h: String
  for +t: List<&2, String>
  for +r: String
  for b: Bool
  for e: {String.is_empty(G.latest.rel.step(b, h, r)) == False{} : Bool}
  for ih: {String.is_empty(r) == False{} : Bool} -> Mem(r, t)
  Mem(G.latest.rel.step(b, h, r), h <> t)

def mem.rel.step(h, t, r, b, e, ih):
  match b:
    case False{}:
      mem.there(h, t, r, ih(e))
    case True{}:
      mem.have(h, t, r, G.ver.of(h), String.is_empty(r), {==}, ih)

# LAW: the release fold answers a name in the list, when it answers one
law latest.rel.mem:
  for +names: List<&2, String>
  for e: {String.is_empty(G.latest.rel(names)) == False{} : Bool}
  Mem(G.latest.rel(names), names)

def latest.rel.mem(names, e):
  match names:
    case []:
      Eq.bit.absurd2(&1, Mem(G.latest.rel([]), []), e)
    case +h <> t:
      mem.rel.step(h, t, G.latest.rel(t), G.release(h), e,
        x => latest.rel.mem(t, x))

# LAW: the choice answers a name in the list, from whichever fold it took
law mem.choose:
  for +names: List<&2, String>
  for c: Bool
  for ec: {String.is_empty(G.latest.rel(names)) == c : Bool}
  for e: {String.is_empty(G.choose.go(c, G.latest.rel(names), G.latest(names)))
    == False{} : Bool}
  Mem(G.choose.go(c, G.latest.rel(names), G.latest(names)), names)

def mem.choose(names, c, ec, e):
  match c:
    case True{}:
      latest.mem(names, e)
    case False{}:
      latest.rel.mem(names, ec)

def Laws.choose_is_a_tag(names, e):
  mem.choose(names, String.is_empty(G.latest.rel(names)), {==}, e)

# The default branch tip. HEAD's row is found by comparing its name, and its
# first field is taken only when it is a commit, so the premise on each
# comparison is rewritten to the arm it picks. A commit is forty characters,
# so it is never the empty answer that passes to the next row.

def Laws.tip_of_head(rev, rest, e):
  match rev:
    case SNil{}:
      Eq.bit.absurd2(&2, {G.tip.rev(G.Row{"", "HEAD"} <> rest) == "" : String}, e)
    case SCon{+c, +t}:
      %e : {G.tip.step(String.is_empty(G.tip.rev.hex(_, SCon{c, t})),
        G.tip.rev.hex(_, SCon{c, t}), _u => G.tip.rev(rest)) == SCon{c, t} : String}
      {==}

def Laws.tip_skips_other(rev, _name, rest, e):
  %e : {G.tip.step(String.is_empty(G.tip.rev.pick(_, G.is_rev(rev), rev)),
    G.tip.rev.pick(_, G.is_rev(rev), rev), _u => G.tip.rev(rest)) == G.tip.rev(rest)
    : String}
  {==}

def Laws.tip_skips_symref(rev, rest, e):
  %e : {G.tip.step(String.is_empty(G.tip.rev.hex(_, rev)), G.tip.rev.hex(_, rev),
    _u => G.tip.rev(rest)) == G.tip.rev(rest) : String}
  {==}
