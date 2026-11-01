# the stages a planner walks and the verdicts that stop it
#
# The plan is `plan.v(decide(w), w)`: `decide` walks the stages a tool
# command passes (a link directory, a cache root, what the target names, its
# place, its commit, its checkout, its ledger, the binary's record) and
# stops, waits or goes on at each; on `Go` the plan is `made(w)`, and every
# other verdict is a plan with no effect that refuses. So a refusal law is a
# case split on the verdict, and a law about a plan that does not refuse is
# a law about `made(w)`, whose parts are each a function of the act, the
# binary's record and what the World resolved. A law that a condition
# refuses walks `decide` stage by stage: every stage before the one that
# checks it either stops or waits, which refuses, or goes on to the next.
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/ledger/manifest.bend as M
import ../../src/git/git.bend as Git
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../src/add/hub.bend as H
import ../../src/ez/target.bend as Tgt
import ../../src/tool/world.bend as TW
import ../../src/tool/plan.bend as TP
import ../../laws/RefusalWritesNothing.bend as L1
import ../../laws/ToolBuiltFileChosen.bend as L2

# LAW: a plan made from a refusal has no effect that writes, whatever the
# upgrade decided around it
law made_refused:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for r: {P.refuses.doc(d) == True{} : Bool}
  {P.writes(P.made(nx, cs, js, d)) == False{} : Bool}

def made_refused(nx, cs, js, d, r):
  match d:
    case P.Doc{text}:
      Eq.bit.absurd(&2, {P.writes(P.made(nx, cs, js, P.Doc{text})) == False{} : Bool}, r)
    case P.Stop{_why}:
      {==}

def L1.lock_refusal_writes_nothing(w, r):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      made_refused(W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}), r)

# a path that ends in a directory's ez.toml holds a `/`
def slash_member(pre: String) -> {Str.clear(pre ++ "/ez.toml", '/') == False{} : Bool}:
  match pre:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      Equal.trans(Bool,
        Bool.and(Bool.not(Char.is_eq(hd, '/')), Str.clear(tl ++ "/ez.toml", '/')),
        Bool.and(Bool.not(Char.is_eq(hd, '/')), False{}),
        False{},
        Equal.cong(Bool, Bool, bb => Bool.and(Bool.not(Char.is_eq(hd, '/')), bb),
          Str.clear(tl ++ "/ez.toml", '/'), False{}, slash_member(tl)),
        Str.and_false(Bool.not(Char.is_eq(hd, '/'))))

# whether a verdict stops the add. Proof vocabulary.
def hstops(v: H.Verdict) -> Bool:
  match v:
    case H.Go{_h, _fs, _ss}:
      False{}
    case H.Pending{_asks}:
      True{}
    case H.Stop{_why}:
      True{}

# LAW: a verdict that stops the add refuses it
law hstops_refuses:
  for v: H.Verdict
  for +w: A.World
  for e: {hstops(v) == True{} : Bool}
  {H.refuses.plan(H.plan.v(v, w)) == True{} : Bool}

def hstops_refuses(v, w, e):
  match v:
    case H.Go{h, fs, ss}:
      Eq.bit.absurd(&2, {H.refuses.plan(H.plan.v(H.Go{h, fs, ss}, w)) == True{} : Bool}, e)
    case H.Pending{_asks}:
      {==}
    case H.Stop{_why}:
      {==}

# LAW: the add stops whenever the arm past the ledger's refusals stops it
law hread_stops:
  for r: M.Read
  for +w: A.World
  for g: {hstops(H.decide.early(String.is_empty(H.early(w)), H.early(w), w)) == True{} : Bool}
  {hstops(H.decide.read(r, w)) == True{} : Bool}

def hread_stops(r, _w, g):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      g

# ---------------------------------------------------------------------------
# a stage that refuses makes the command refuse
#
# Each lemma below says: if the stage that checks the condition refuses,
# then so does every stage before it, since each either stops, waits, or
# goes on to the next. `pre_*` walks up to where the place is decided;
# `co_*` walks from there to where the checkout is decided.

law pre_pin:
  for ok: Bool
  for +n: String
  for +r: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.pin(ok, n, r, w), w)) == True{} : Bool}

def pre_pin(ok, _n, _r, _w, h):
  match ok:
    case True{}:
      h
    case False{}:
      {==}

law pre_src:
  for s: TP.Src
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.src(s, w), w)) == True{} : Bool}

def pre_src(s, w, h):
  match s:
    case TP.Pin{+n, _u, +r, _o}:
      pre_pin(Git.is_rev(r), n, r, w, h)
    case TP.Free{_pl}:
      h
    case TP.NoSrc{_why}:
      {==}

law pre_root:
  for m: Maybe<&2, String>
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.root(m, w), w)) == True{} : Bool}

def pre_root(m, w, h):
  match m:
    case None{}:
      {==}
    case Some{_r}:
      pre_src(TP.src(w), w, h)

law pre_bin:
  for b: Bool
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.bin(b, w), w)) == True{} : Bool}

def pre_bin(b, w, h):
  match b:
    case True{}:
      {==}
    case False{}:
      pre_root(TW.cache.of(w), w, h)

# LAW: a World whose place refuses refuses
law pre:
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}
  {TP.refuses(w) == True{} : Bool}

def pre(w, h):
  pre_bin(Bool.and(TP.links.act(TW.act(w)), TP.none(TW.bin.of(TW.env(w)))), w, h)

law co_tip:
  for ok: Bool
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.tip(ok, url, w), w)) == True{} : Bool}

def co_tip(ok, _url, _w, h):
  match ok:
    case True{}:
      h
    case False{}:
      {==}

law co_said:
  for s: Up.Said
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.said(s, url, w), w)) == True{} : Bool}

def co_said(s, url, w, h):
  match s:
    case Up.Said{_text}:
      co_tip(Git.is_rev(TP.rev(w)), url, w, h)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law co_head:
  for s: TP.Src
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.head(s, url, w), w)) == True{} : Bool}

def co_head(s, url, w, h):
  match s:
    case TP.Pin{_n, _u, _r, _o}:
      h
    case TP.Free{_pl}:
      co_said(TP.head.said(w, url), url, w, h)
    case TP.NoSrc{_why}:
      {==}

law co_slug:
  for ok: Bool
  for +url: String
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.slug(ok, url, w), w)) == True{} : Bool}

def co_slug(ok, url, w, h):
  match ok:
    case True{}:
      co_head(TP.src(w), url, w, h)
    case False{}:
      {==}

law co_loc:
  for l: TP.Loc
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.loc(l, w), w)) == True{} : Bool}

def co_loc(l, _w, h):
  match l:
    case TP.Loc{_a, _t, _h, _ok, _s}:
      h
    case TP.LocWait{_ask}:
      {==}
    case TP.LocNo{_why}:
      {==}

law co_place:
  for pl: Tgt.Place
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.co(TP.co(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.place(pl, w), w)) == True{} : Bool}

def co_place(pl, w, h):
  match pl:
    case Tgt.Bad{_why}:
      {==}
    case Tgt.Local{+p}:
      co_loc(TP.loc(p, w), w, h)
    case Tgt.Remote{+url, +slug}:
      co_slug(Tgt.slug.ok(slug), url, w, h)

# ---------------------------------------------------------------------------
# laws/ToolBuiltFileChosen.bend: a file to build that is not in the checkout
#
# `fin_*` walks from the checkout to the stage that asks whether the file is
# there: every stage before it stops, waits, or goes on to the next.

law fin_name:
  for ok: Bool
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.name(ok, w), w)) == True{} : Bool}

def fin_name(ok, _w, h):
  match ok:
    case True{}:
      h
    case False{}:
      {==}

law fin_led:
  for r: M.Read
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.led(r, w), w)) == True{} : Bool}

def fin_led(r, w, h):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      fin_name(TP.name.ok(TP.name.raw(w)), w, h)

law fin_co:
  for c: TP.Co
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.co(c, w), w)) == True{} : Bool}

def fin_co(c, w, h):
  match c:
    case TP.Kept{_t, _l}:
      fin_led(TP.led(w), w, h)
    case TP.Laid{_fs}:
      fin_led(TP.led(w), w, h)
    case TP.CoWait{_as, _us}:
      {==}
    case TP.CoNo{_why}:
      {==}

# LAW: a World whose stage that asks for the file refuses refuses
law fin:
  for +w: TW.World
  for h: {TP.refuses.plan(TP.plan.v(TP.decide.file(TP.file.asks(w), w), w)) == True{} : Bool}
  {TP.refuses(w) == True{} : Bool}

def fin(w, h):
  pre(w, co_place(TP.place(w), w, fin_co(TP.co(w), w, h)))

law gone_file:
  for open: List<&2, TW.Ask>
  for +w: TW.World
  for miss: {TP.present(w) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.file(open, w), w)) == True{} : Bool}

def gone_file(open, w, miss):
  match open:
    case []:
      %Equal.sym(Bool, TP.present(w), False{}, miss)
        : {TP.refuses.plan(TP.plan.v(TP.decide.present(_, w), w)) == True{} : Bool}
      {==}
    case _h <> _t:
      {==}

def L2.tool_refuses_missing_entry(w, miss):
  fin(w, gone_file(TP.file.asks(w), w, miss))
