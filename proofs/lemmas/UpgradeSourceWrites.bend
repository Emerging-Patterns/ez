# what an upgrade leaves at each source it rewrites, and at every other path
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/upgrade.bend as U
import ../../src/lock/lock.bend as L
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../laws/UpgradeRewritesSources.bend as L1
import ../../laws/defs/WorldAfterLock.bend as D1
import ./AllowlistBlock.bend as M1
import ./PlanEffectFacts.bend as M2
import ./UpgradeWritesAroundLedger.bend as M3

# LAW: none of the upgrade's own files is at a path that is neither ez.toml
# nor `.gitignore`
law ok_go_empty:
  for a: Bool
  for b: Bool
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  for h: M3.ok.go(a, b, t, vs, model, ig)
  Empty

def ok_go_empty(a, b, _t, _vs, _model, _ig, ea, eb, h):
  match a b:
    case True{} _:
      Eq.bit.absurd2(&1, Empty, ea)
    case False{} True{}:
      Eq.bit.absurd2(&1, Empty, eb)
    case False{} False{}:
      h

# LAW: one of the upgrade's own files, with how its path compares to another
# given as a parameter: it is not at a path that is neither of its two
law other_ne:
  for +q: String
  for +p: String
  for c: Bool
  for +ec: {String.eq(q, p) == c : Bool}
  for +t: String
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: M3.ok.go(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t, vs, model, ig)
  for +n1: {String.eq(p, "ez.toml") == False{} : Bool}
  for +n2: {String.eq(p, ".gitignore") == False{} : Bool}
  {String.eq(q, p) == False{} : Bool}

def other_ne(q, p, c, ec, t, vs, model, ig, h, n1, n2):
  match c:
    case False{}:
      ec
    case True{}:
      Empty.absurd({String.eq(q, p) == False{} : Bool},
        ok_go_empty(String.eq(q, "ez.toml"), String.eq(q, ".gitignore"), t, vs, model, ig,
          Equal.trans(Bool, String.eq(q, "ez.toml"), String.eq(p, "ez.toml"), False{},
            Equal.cong(String, Bool, x => String.eq(x, "ez.toml"), q, p,
              Str.string_eq_true(q, p, ec)), n1),
          Equal.trans(Bool, String.eq(q, ".gitignore"), String.eq(p, ".gitignore"), False{},
            Equal.cong(String, Bool, x => String.eq(x, ".gitignore"), q, p,
              Str.string_eq_true(q, p, ec)), n2),
          h))

# LAW: the upgrade's own files leave every other path as it was
law edits_other:
  for es: List<&2, Up.Edit>
  for +vs: List<&2, String>
  for +model: M.Read
  for +ig: String
  for h: M3.ok.edits(es, vs, model, ig)
  for +rest: List<&2, P.Effect>
  for +p: String
  for +n1: {String.eq(p, "ez.toml") == False{} : Bool}
  for +n2: {String.eq(p, ".gitignore") == False{} : Bool}
  {P.put.in(P.edits.of(es, rest), p) == P.put.in(rest, p) : P.Wrote}

def edits_other(es, vs, model, ig, h, rest, p, n1, n2):
  match es:
    case []:
      {==}
    case Up.Edit{+q, +t} <> +tl:
      (h1, h2) = h
      Equal.trans(P.Wrote,
        P.put.one(P.Write{q, t}, p, P.put.in(P.edits.of(tl, rest), p)),
        P.put.in(P.edits.of(tl, rest), p),
        P.put.in(rest, p),
        M1.put_one_other(q, t, p, P.put.in(P.edits.of(tl, rest), p),
          other_ne(q, p, String.eq(q, p), {==}, t, vs, model, ig, h1, n1, n2)),
        edits_other(tl, vs, model, ig, h2, rest, p, n1, n2))

# LAW: sources in front of one, none of which is at its path, leave what it
# gets as it is
law src_pre:
  for pre: List<&2, Up.Found>
  for +xs: List<&2, Up.Found>
  for +sw: List<&2, U.Swap>
  for +rest: List<&2, P.Effect>
  for +p: String
  for +m: {D1.found.miss(pre, p) == True{} : Bool}
  {P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, pre, xs), sw), rest), p)
    == P.put.in(P.edits.of(Up.edit.sources(xs, sw), rest), p) : P.Wrote}

def src_pre(pre, xs, sw, rest, p, m):
  match pre:
    case []:
      {==}
    case Up.Found{+a, +x} <> +tl:
      Equal.trans(P.Wrote,
        P.put.in(P.edits.of(Up.edit.if(String.eq(U.reimport.many(sw, x), x), a,
          U.reimport.many(sw, x), Up.edit.sources(List.append(&2, Up.Found, tl, xs), sw)),
          rest), p),
        P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, tl, xs), sw), rest), p),
        P.put.in(P.edits.of(Up.edit.sources(xs, sw), rest), p),
        M3.src_miss.arm(String.eq(U.reimport.many(sw, x), x), a, U.reimport.many(sw, x),
          Up.edit.sources(List.append(&2, Up.Found, tl, xs), sw), rest, p,
          Eq.not.true(String.eq(a, p),
            Eq.and.left(Bool.not(String.eq(a, p)), D1.found.miss(tl, p), m))),
        src_pre(tl, xs, sw, rest, p,
          Eq.and.right(Bool.not(String.eq(a, p)), D1.found.miss(tl, p), m)))

# what a source leaves at its path: nothing when the moves left its text as
# it was, and the rewritten text otherwise. Law vocabulary: ez never calls it.
def wrote.of(same: Bool, +t: String) -> P.Wrote:
  match same:
    case True{}:
      P.Kept{}
    case False{}:
      P.Put{t}

# LAW: one source, with whether the moves change it given as a parameter,
# written where nothing after it writes its path
law src_one.arm:
  for b: Bool
  for +at: String
  for +m: String
  for +es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  for kr: {P.put.in(P.edits.of(es, rest), at) == P.Kept{} : P.Wrote}
  {P.put.in(P.edits.of(Up.edit.if(b, at, m, es), rest), at) == wrote.of(b, m) : P.Wrote}

def src_one.arm(b, at, m, es, rest, kr):
  match b:
    case True{}:
      kr
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.edits.of(es, rest), at), P.Kept{}, kr)
        : {P.put.one(P.Write{at, m}, at, _) == P.Put{m} : P.Wrote}
      %Equal.sym(Bool, String.eq(at, at), True{}, Eq.string_eq_self(at))
        : {Bool.pick(P.Wrote, _, P.Put{m}, P.Kept{}) == P.Put{m} : P.Wrote}
      {==}

# LAW: a source the World names once is written with its text rewritten, or
# not written when the moves leave it as it was
law src_all:
  for +pre: List<&2, Up.Found>
  for +at: String
  for +text: String
  for +post: List<&2, Up.Found>
  for +sw: List<&2, U.Swap>
  for +rest: List<&2, P.Effect>
  for +mp: {D1.found.miss(pre, at) == True{} : Bool}
  for +mq: {D1.found.miss(post, at) == True{} : Bool}
  for +kr: {P.put.in(rest, at) == P.Kept{} : P.Wrote}
  {P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, pre,
    Up.Found{at, text} <> post), sw), rest), at)
    == wrote.of(String.eq(U.reimport.many(sw, text), text), U.reimport.many(sw, text))
    : P.Wrote}

def src_all(pre, at, text, post, sw, rest, mp, mq, kr):
  Equal.trans(P.Wrote,
    P.put.in(P.edits.of(Up.edit.sources(List.append(&2, Up.Found, pre,
      Up.Found{at, text} <> post), sw), rest), at),
    P.put.in(P.edits.of(Up.edit.sources(Up.Found{at, text} <> post, sw), rest), at),
    wrote.of(String.eq(U.reimport.many(sw, text), text), U.reimport.many(sw, text)),
    src_pre(pre, Up.Found{at, text} <> post, sw, rest, at, mp),
    src_one.arm(String.eq(U.reimport.many(sw, text), text), at, U.reimport.many(sw, text),
      Up.edit.sources(post, sw), rest,
      Equal.trans(P.Wrote, P.put.in(P.edits.of(Up.edit.sources(post, sw), rest), at),
        P.put.in(rest, at), P.Kept{}, M3.src_miss(post, sw, rest, at, mq), kr)))

# LAW: a path that ends `.bend` is none of the paths that do not, with how
# they compare given as a parameter
law not_bend.arm:
  for +lit: String
  for +at: String
  for c: Bool
  for ec: {String.eq(at, lit) == c : Bool}
  for lb: {String.ends_with(lit, ".bend") == False{} : Bool}
  for bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {String.eq(at, lit) == False{} : Bool}

def not_bend.arm(lit, at, c, ec, lb, bend):
  match c:
    case False{}:
      ec
    case True{}:
      Eq.bit.absurd2(&2, {String.eq(at, lit) == False{} : Bool},
        Equal.trans(Bool, True{}, String.ends_with(lit, ".bend"), False{},
          Equal.trans(Bool, True{}, String.ends_with(at, ".bend"), String.ends_with(lit, ".bend"),
            Equal.sym(Bool, String.ends_with(at, ".bend"), True{}, bend),
            Equal.cong(String, Bool, x => String.ends_with(x, ".bend"), at, lit,
              Str.string_eq_true(at, lit, ec))),
          lb))

law not_bend:
  for +lit: String
  for +at: String
  for lb: {String.ends_with(lit, ".bend") == False{} : Bool}
  for bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {String.eq(at, lit) == False{} : Bool}

def not_bend(lit, at, lb, bend):
  not_bend.arm(lit, at, String.eq(at, lit), {==}, lb, bend)

# LAW: and the other way round
law not_bend.flip:
  for +lit: String
  for +at: String
  for lb: {String.ends_with(lit, ".bend") == False{} : Bool}
  for bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {String.eq(lit, at) == False{} : Bool}

def not_bend.flip(lit, at, lb, bend):
  M3.eq_flip(at, lit, not_bend(lit, at, lb, bend))

# LAW: the lock, written last, is not at a source's path
law lock_kept:
  for +at: String
  for +lt: String
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {P.put.in([P.Write{P.lockfile(), lt}], at) == P.Kept{} : P.Wrote}

def lock_kept(at, lt, bend):
  M1.put_one_other("ez.lock.toml", lt, at, P.Kept{}, not_bend.flip("ez.lock.toml", at, {==}, bend))

# LAW: the sources' writes, and the lock after them, leave at a source's path
# the World names once what its own write leaves
law src_after:
  for +nx: Up.Next
  for +lt: String
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {D1.found.miss(pre, at) == True{} : Bool}
  for +mq: {D1.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at)
    == wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
      U.reimport.many(Up.next.swaps(nx), text)) : P.Wrote}

def src_after(nx, lt, at, text, pre, post, efs, mp, mq, bend):
  %Equal.sym(List<&2, Up.Found>, Up.next.found(nx),
    List.append(&2, Up.Found, pre, Up.Found{at, text} <> post), efs)
    : {P.put.in(P.edits.of(Up.edit.sources(_, Up.next.swaps(nx)),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at)
      == wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
        U.reimport.many(Up.next.swaps(nx), text)) : P.Wrote}
  src_all(pre, at, text, post, Up.next.swaps(nx),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), mp, mq,
    Equal.trans(P.Wrote,
      P.put.in(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]), at),
      P.put.in([P.Write{P.lockfile(), lt}], at),
      P.Kept{},
      M2.drops_put(Up.next.drops(nx), [P.Write{P.lockfile(), lt}], at),
      lock_kept(at, lt, bend)))

# LAW: a made plan leaves at a source's path what the sources' writes leave
# there
law made_src:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +lt: String
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for +ig: String
  for okn: M3.ok.next(nx, ig)
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {D1.found.miss(pre, at) == True{} : Bool}
  for +mq: {D1.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  {P.put.plan(P.made(nx, cs, js, P.Doc{lt}), at)
    == wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
      U.reimport.many(Up.next.swaps(nx), text)) : P.Wrote}

def made_src(nx, cs, js, lt, at, text, pre, post, ig, okn, efs, mp, mq, bend):
  Equal.trans(P.Wrote,
    P.put.in(P.says.of(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
      P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))))), at),
    P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
      Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at),
    wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
      U.reimport.many(Up.next.swaps(nx), text)),
    Equal.trans(P.Wrote,
      P.put.in(P.says.of(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))))), at),
      P.put.in(P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), at),
      P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at),
      M2.says_put(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))), at),
      M2.lays_names_put(cs, Up.next.vends(nx), js, L.names.read(lt),
        P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
          Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at)),
    Equal.trans(P.Wrote,
      P.put.in(P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))), at),
      P.put.in(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at),
      wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
        U.reimport.many(Up.next.swaps(nx), text)),
      edits_other(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig, okn,
        P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
          P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])), at,
        not_bend("ez.toml", at, {==}, bend), not_bend(".gitignore", at, {==}, bend)),
      src_after(nx, lt, at, text, pre, post, efs, mp, mq, bend)))

# LAW: what a source leaves, rewritten or not written, is its rewritten text
law left_of:
  for b: Bool
  for +m: String
  for +text: String
  for eb: {String.eq(m, text) == b : Bool}
  {D1.left.at(wrote.of(b, m), text) == m : String}

def left_of(b, m, text, eb):
  match b:
    case True{}:
      Equal.sym(String, m, text, Str.string_eq_true(m, text, eb))
    case False{}:
      {==}

# LAW: a plan that is made leaves at a `.bend` source the World names once its
# text with every moved hash rewritten; a refusal is not made
law rw_arm:
  for d: P.Doc
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for +ig: String
  for okn: M3.ok.next(nx, ig)
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {D1.found.miss(pre, at) == True{} : Bool}
  for +mq: {D1.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses.doc(d) == False{} : Bool}
  {D1.left.at(P.put.plan(P.made(nx, cs, js, d), at), text)
    == U.reimport.many(Up.next.swaps(nx), text) : String}

def rw_arm(d, nx, cs, js, at, text, pre, post, ig, okn, efs, mp, mq, bend, ok):
  match d:
    case P.Stop{_why}:
      Eq.bit.absurd2(&2, {D1.left.at(P.Kept{}, text) == U.reimport.many(Up.next.swaps(nx), text)
        : String}, ok)
    case P.Doc{+lt}:
      %Equal.sym(P.Wrote, P.put.plan(P.made(nx, cs, js, P.Doc{lt}), at),
        wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
          U.reimport.many(Up.next.swaps(nx), text)),
        made_src(nx, cs, js, lt, at, text, pre, post, ig, okn, efs, mp, mq, bend))
        : {D1.left.at(_, text) == U.reimport.many(Up.next.swaps(nx), text) : String}
      left_of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
        U.reimport.many(Up.next.swaps(nx), text), text, {==})

def L1.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      rw_arm(P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        at, text, pre, post, D1.ignore.said(Up.text.said(ups, Up.Ignore{})),
        M3.ok_world(args, ledger, ups), fs, mp, mq, bend, ok)
