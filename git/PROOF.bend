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
