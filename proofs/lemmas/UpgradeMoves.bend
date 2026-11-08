# the upgrade's moves, one fact about each dependency's fate
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/upgrade.bend as U
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../laws/defs/LockInputs.bend as D1
import ./LockPlannerFacts.bend as M1

# The upgrade's moves (laws/UpgradeRevMovesForward.bend,
# laws/UpgradeTagFollows.bend). Each law is one fact about one dependency's
# fate (`Up.dep.one`), carried through the walk over the ledger's
# dependencies (`Up.deps.walk`) to the ledger model the upgrade renders
# (`Up.next.model`). A fate is proved sound once for any remote tip, since a
# tag's and the default branch's are read the same way from there on
# (`Up.dep.tip`).

# a pin from a repository, with its fields spelled out
def mv.git(
  +hn: String,
  +hh: String,
  +he: String,
  +url: String,
  +rev: String,
  +tag: String,
  +root: String,
  +nar: String,
  +vend: Bool
) -> M.Dep:
  M.Dep{hn, hh, he, M.Git{url, rev, tag, root, nar, vend}}

# a fate is sound against a tip when the pin it leaves is kept or moved
# along its history, as `moved.ok` reads the remote
def mv.ok(fate: Up.Fate, +t: Up.Tip, +rs: List<&2, Up.Reply>, +old: M.Dep) -> Bool:
  match fate:
    case Up.Became{d, _o, _n, _p, _m, _s, _t}:
      D1.moved.ok(t, rs, old, d)
    case Up.Waits{_asks}:
      True{}
    case Up.Halts{_why}:
      True{}

# whether a fate refuses
def mv.halts(fate: Up.Fate) -> Bool:
  match fate:
    case Up.Became{_d, _o, _n, _p, _m, _s, _t}:
      False{}
    case Up.Waits{_asks}:
      False{}
    case Up.Halts{_why}:
      True{}

# the walk is sound for the dependency named `n`: it refuses, or still asks,
# or the dependency it leaves under that name is sound against `old`
def mv.walk(+t: Up.Tip, +rs: List<&2, Up.Reply>, dd: Up.Deps, +old: M.Dep, +n: String) -> Bool:
  Up.Deps{ds, _ss, _es, _m, _sy, _tr, asks, bad} = dd
  Bool.or(Bool.not(String.is_empty(bad)),
    Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)), D1.moved.ok(t, rs, old, M.find(ds, n))))

# the walk's refusal, "" for none
def mv.bad(dd: Up.Deps) -> String:
  Up.Deps{_ds, _ss, _es, _m, _sy, _tr, _asks, bad} = dd
  bad

# whether an upgrade refuses
def mv.stops(nx: Up.Next) -> Bool:
  Bool.not(String.is_empty(Up.next.stop(nx)))

# the dependency named `n` in the ledger model an upgrade renders
def mv.dep(nx: Up.Next, +n: String) -> M.Dep:
  M.dep(Up.next.model(nx), n)

# LAW: a pin kept as it was is sound against any tip
law mv.self:
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {D1.moved.ok(t, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend),
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.self(t, rs, _hn, _hh, _he, url, rev, tag, _root, _nar, _vend):
  Equal.trans(Bool,
    Bool.and(String.eq(tag, tag),
      Bool.or(String.eq(rev, rev), D1.moved.onto(t, rs, url, rev, rev))),
    Bool.or(String.eq(rev, rev), D1.moved.onto(t, rs, url, rev, rev)),
    True{},
    Equal.cong(Bool, Bool,
      x => Bool.and(x, Bool.or(String.eq(rev, rev), D1.moved.onto(t, rs, url, rev, rev))),
      String.eq(tag, tag), True{}, Eq.string_eq_self(tag)),
    Equal.cong(Bool, Bool, x => Bool.or(x, D1.moved.onto(t, rs, url, rev, rev)),
      String.eq(rev, rev), True{}, Eq.string_eq_self(rev)))

# LAW: and so is any pin from a repository
law mv.self_dep:
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +d: M.Dep
  for g: {M.source.is_git(M.source.dep(d)) == True{} : Bool}
  {D1.moved.ok(t, rs, d, d) == True{} : Bool}

def mv.self_dep(t, rs, d, g):
  match d:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          g
        case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
          mv.self(t, rs, hn, hh, he, url, rev, tag, root, nar, vend)
        case M.Member{mp, mn}:
          g

# One pin's fate is sound against the tip it was moved by. The pin is
# checked out when the tip is its own commit, and kept only when the checkout
# agrees; it is moved only to a tip the remote says descends from it, once
# the tip's checkout and the hub's word are in.

# LAW: a pin moved to the tip, once the hub has not objected
law mv.ok_hub:
  for hb: Up.Hubbed
  for +rs: List<&2, Up.Reply>
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +hash: String
  for +r: String
  for +tg: String
  for +br: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  for e: {Up.onward(rs, Up.Above{url, rev, r}) == Up.Asc{True{}} : Up.Asc}
  {mv.ok(Up.dep.hub(hb, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), hash, r, root2,
    nar2, man, srcs, br), Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend))
    == True{} : Bool}

def mv.ok_hub(
  hb,
  rs,
  _hn,
  _hh,
  _he,
  url,
  rev,
  tag,
  _root,
  _nar,
  _vend,
  _hash,
  r,
  _tg,
  _br,
  _root2,
  _nar2,
  _man,
  _srcs,
  e
):
  match hb:
    case Up.Clear{}:
      Equal.trans(Bool,
        Bool.and(String.eq(tag, tag), Bool.or(String.eq(r, rev),
          Bool.and(String.eq(r, r), D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))))),
        Bool.or(String.eq(r, rev),
          Bool.and(String.eq(r, r), D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r})))),
        True{},
        Equal.cong(Bool, Bool, x => Bool.and(x, Bool.or(String.eq(r, rev),
          Bool.and(String.eq(r, r), D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))))),
          String.eq(tag, tag), True{}, Eq.string_eq_self(tag)),
        M1.mv.or_r(String.eq(r, rev),
          Bool.and(String.eq(r, r), D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))),
          Equal.trans(Bool,
            Bool.and(String.eq(r, r), D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))),
            D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r})),
            True{},
            Equal.cong(Bool, Bool,
              x => Bool.and(x, D1.onward.yes(Up.onward(rs, Up.Above{url, rev, r}))),
              String.eq(r, r), True{}, Eq.string_eq_self(r)),
            Equal.cong(Up.Asc, Bool, a => D1.onward.yes(a),
              Up.onward(rs, Up.Above{url, rev, r}), Up.Asc{True{}}, e))))
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved to the tip, once its checkout is in
law mv.ok_adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  for e: {Up.onward(rs, Up.Above{url, rev, r}) == Up.Asc{True{}} : Up.Asc}
  {mv.ok(Up.dep.advance(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, br),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_adv(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br, e):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      mv.ok_hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), rs, hn, hh, he, url, rev, tag,
        root, nar, vend, Up.hash.of(man), r, tg, br, root2, nar2, man, srcs, e)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: a tip that is another commit, once the remote said whether it
# descends from the pin
law mv.ok_onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  for e: {Up.onward(rs, Up.Above{url, rev, r}) == a : Up.Asc}
  {mv.ok(Up.dep.onward(a, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, tg, br),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_onward(a, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br, e):
  match a:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          mv.ok_adv(Up.checkout(rs, Up.Tree{url, r, he}), rs, hub, hn, hh, he, url, rev, tag,
            root, nar, vend, r, tg, br, e)
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the pin's own commit, judged by whether its checkout agrees
law mv.ok_agree:
  for g: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  for +seen: String
  {mv.ok(Up.dep.verdict(U.judge(True{}, True{}, g, r, tg), rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, "", seen),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_agree(g, rs, _hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br, _seen):
  match g:
    case True{}:
      mv.self(Up.At{r, tg, br}, rs, hn, hh, he, url, rev, tag, root, nar, vend)
    case False{}:
      {==}

# LAW: the pin's own commit, once its checkout is in
law mv.ok_kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  {mv.ok(Up.dep.kept(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, tg),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_kept(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      mv.ok_agree(U.agree(hh, Up.hash.kept(hh, man), nar, nar2, root, root2), rs, hub, hn, hh, he,
        url, rev, tag, root, nar, vend, r, tg, br, Up.hash.kept(hh, man))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: the tip against the pin: its own commit, or another
law mv.ok_same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +r: String
  for +tg: String
  for +br: String
  {mv.ok(Up.dep.same(s, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), r, tg, br),
    Up.At{r, tg, br}, rs, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_same(s, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br):
  match s:
    case True{}:
      mv.ok_kept(Up.checkout(rs, Up.Tree{url, rev, he}), rs, hub, hn, hh, he, url, rev, tag,
        root, nar, vend, r, tg, br)
    case False{}:
      mv.ok_onward(Up.onward(rs, Up.Above{url, rev, r}), rs, hub, hn, hh, he, url, rev, tag,
        root, nar, vend, r, tg, br, {==})

# LAW: a pin is sound against whatever tip the remote named
law mv.ok_tip:
  for t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {mv.ok(Up.dep.tip(t, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)), t, rs,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.ok_tip(t, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend):
  match t:
    case Up.At{+r, +tg, +br}:
      mv.ok_same(String.eq(rev, r), rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, r, tg, br)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# The walk over the ledger's dependencies. `M.find` answers the first
# dependency of a name, and every fate keeps its name, so the walk leaves the
# named dependency where the ledger had it, unless it refused or still asks.

# LAW: a walk over no dependencies: the blank pin `M.find` answers is never
# sound, so neither side holds
law mv.walk_nil:
  for s: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for pre: {mv.ok(Up.dep.one(U.aim(s, M.Hub{""}), rs, only, hub, M.Dep{"", "", "", M.Hub{""}}), t, rs,
    M.Dep{"", "", "", M.Hub{""}}) == True{} : Bool}
  {mv.walk(t, rs, Up.deps.walk(rs, only, hub, []), M.Dep{"", "", "", M.Hub{""}}, n) == True{} : Bool}

def mv.walk_nil(s, _t, _rs, _only, _hub, _n, pre):
  match s:
    case True{}:
      pre
    case False{}:
      pre

# LAW: the named dependency's fate in front of the rest
law mv.join_hit:
  for f: Up.Fate
  for rest: Up.Deps
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for e: {String.eq(hn, n) == True{} : Bool}
  for ok: {mv.ok(f, t, rs, M.Dep{hn, hh, he, src}) == True{} : Bool}
  for fn: {M1.mv.fine(f, hn) == (hn, True{}) : String & Bool}
  {mv.walk(t, rs, Up.deps.join(f, rest), M.Dep{hn, hh, he, src}, n) == True{} : Bool}

def mv.join_hit(f, rest, t, rs, n, hn, hh, he, src, e, ok, fn):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, _, _, _} Up.Deps{+ds, _, _, _, _, _, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, M.Dep{hn, hh, he, src},
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, M.Dep{hn, hh, he, src},
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              D1.moved.ok(t, rs, M.Dep{hn, hh, he, src},
                M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          dn, hn, Equal.cong(String & Bool, String, p => M1.mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            D1.moved.ok(t, rs, M.Dep{hn, hh, he, src},
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            D1.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.Dep{dn, dh, de, dsrc}))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)),
              Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
                D1.moved.ok(t, rs, M.Dep{hn, hh, he, src},
                  M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
            String.eq(hn, n), True{}, e),
          M1.mv.or_r(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              D1.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.Dep{dn, dh, de, dsrc})),
            M1.mv.or_r(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              D1.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.Dep{dn, dh, de, dsrc}), ok))))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.find(ds, n)))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => M1.mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      M1.mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, _bad}:
      M1.mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, M.Dep{hn, hh, he, src}, M.find(ds, n))),
        M1.mv.halt_not(why))

# LAW: another dependency's fate in front of the rest
law mv.join_miss:
  for f: Up.Fate
  for rest: Up.Deps
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +hn: String
  for +old: M.Dep
  for e: {String.eq(hn, n) == False{} : Bool}
  for fn: {M1.mv.fine(f, hn) == (hn, True{}) : String & Bool}
  for ih: {mv.walk(t, rs, rest, old, n) == True{} : Bool}
  {mv.walk(t, rs, Up.deps.join(f, rest), old, n) == True{} : Bool}

def mv.join_miss(f, rest, t, rs, n, hn, old, e, fn, ih):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, _, _, _} Up.Deps{+ds, _, _, _, _, _, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, old,
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, old,
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              D1.moved.ok(t, rs, old,
                M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          dn, hn, Equal.cong(String & Bool, String, p => M1.mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            D1.moved.ok(t, rs, old,
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            D1.moved.ok(t, rs, old, M.find(ds, n)))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)),
              Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
                D1.moved.ok(t, rs, old, M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n))))),
            String.eq(hn, n), False{}, e),
          ih))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          D1.moved.ok(t, rs, old, M.find(ds, n)))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => M1.mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      M1.mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, _any, _sy, _tr, +asks, _bad}:
      M1.mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)), D1.moved.ok(t, rs, old, M.find(ds, n))),
        M1.mv.halt_not(why))

# LAW: one step of the walk, whether or not its head is the named dependency
law mv.walk_step:
  for b: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for e: {String.eq(hn, n) == b : Bool}
  for pre: {mv.ok(Up.dep.one(U.aim(U.chosen(only,
    M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))),
    M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))), rs, only, hub,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))), t, rs,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))) == True{} : Bool}
  for ih: {mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(tl, n))),
    M.source.dep(M.find(tl, n))), rs, only, hub, M.find(tl, n)), t, rs, M.find(tl, n))
    == True{} : Bool}
    -> {mv.walk(t, rs, Up.deps.walk(rs, only, hub, tl), M.find(tl, n), n) == True{} : Bool}
  {mv.walk(t, rs, Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub,
    M.Dep{hn, hh, he, src}), Up.deps.walk(rs, only, hub, tl)),
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)), n) == True{} : Bool}

def mv.walk_step(b, t, rs, only, hub, n, hn, hh, he, src, tl, e, pre, ih):
  match b:
    case True{}:
      mv.join_hit(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), t, rs, n, hn, hh, he, src, e, pre,
        M1.mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}))
    case False{}:
      mv.join_miss(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), t, rs, n, hn, M.find(tl, n), e,
        M1.mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}), ih(pre))

# LAW: the walk is sound for the named dependency when its fate is
law mv.walk_ok:
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +ds: List<&2, M.Dep>
  for pre: {mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(ds, n))),
    M.source.dep(M.find(ds, n))), rs, only, hub, M.find(ds, n)), t, rs, M.find(ds, n))
    == True{} : Bool}
  {mv.walk(t, rs, Up.deps.walk(rs, only, hub, ds), M.find(ds, n), n) == True{} : Bool}

def mv.walk_ok(t, rs, only, hub, n, ds, pre):
  match ds:
    case []:
      mv.walk_nil(U.chosen(only, ""), t, rs, only, hub, n, pre)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.walk_step(String.eq(hn, n), t, rs, only, hub, n, hn, hh, he, src, tl, {==}, pre,
            p => mv.walk_ok(t, rs, only, hub, n, tl, p))

# The ledger model the upgrade renders. Every way the upgrade can end leaves
# ez.toml's model as it was, except the one where every pin was answered and
# one moved, which leaves the dependencies the walk left.

# LAW: the model, once it is known whether a pin moved
law mv.model_moved:
  for moved: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Cli>
  for wk: {D1.moved.ok(t, rs, M.find(ds, n), M.find(dds, n)) == True{} : Bool}
  for self: {D1.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {D1.moved.ok(t, rs, M.find(ds, n), M.dep(Up.model.next(moved,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
      ts}), n))
    == True{} : Bool}

def mv.model_moved(moved, _t, _rs, _n, _name, _entry, _bin, _hub, _hubpa, _hubpv, _ds, _ts, _dds, _tts, wk, self):
  match moved:
    case True{}:
      wk
    case False{}:
      self

# LAW: the model, once the sources are known
law mv.model_srcs:
  for srcs: Up.Srcs
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +ig: String
  for wk: {D1.moved.ok(t, rs, M.find(ds, n), M.find(dds, n)) == True{} : Bool}
  for self: {D1.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {D1.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), n))
    == True{} : Bool}

def mv.model_srcs(
  srcs,
  t,
  rs,
  n,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  _ss,
  _es,
  dm,
  _dsy,
  _dtr,
  tts,
  tm,
  _tsy,
  _ig,
  wk,
  self
):
  match srcs:
    case Up.Srcs{_fs}:
      mv.model_moved(Bool.or(dm, tm), t, rs, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, tts, wk, self)
    case Up.SrcsWait{_ask}:
      self
    case Up.SrcsNo{_why}:
      self

# LAW: the model, once `.gitignore` is known
law mv.model_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for wk: {D1.moved.ok(t, rs, M.find(ds, n), M.find(dds, n)) == True{} : Bool}
  for self: {D1.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {D1.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.got.ignore(said, srcs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), n))
    == True{} : Bool}

def mv.model_ignore(
  said,
  srcs,
  t,
  rs,
  n,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  ss,
  es,
  dm,
  dsy,
  dtr,
  tts,
  tm,
  tsy,
  wk,
  self
):
  match said:
    case Up.Said{+ig}:
      mv.model_srcs(srcs, t, rs, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dm, dsy, dtr, tts,
        tm, tsy, ig, wk, self)
    case Up.Unsaid{_why}:
      self
    case Up.Unasked{_ask}:
      self

# LAW: the model, once the pins are answered or refused
law mv.model_pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for wk: {mv.walk(t, rs, dd, M.find(ds, n), n) == True{} : Bool}
  for self: {D1.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {D1.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.pins(dd, tt, rs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), n)) == True{} : Bool}

def mv.model_pins(dd, tt, t, rs, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, wk, self):
  match dd tt:
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SCon{_c, _cs}} Up.Tools{_tts, _tm, _tsy, _tasks, _tbad}:
      self
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SCon{_c, _cs}}:
      self
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _a <> _as, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SNil{}}:
      self
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, [], SNil{}} Up.Tools{_tts, _tm, _tsy, _a <> _as, SNil{}}:
      self
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      mv.model_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), t, rs, n, name, entry,
        bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dm, dsy, dtr, tts, tm, tsy, wk, self)

# LAW: the model, once `--package` is known to name something
law mv.model_known:
  for k: Bool
  for +t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for wk: {mv.walk(t, rs, Up.deps.walk(rs, only, M.hub.or(hub), ds), M.find(ds, n), n)
    == True{} : Bool}
  for self: {D1.moved.ok(t, rs, M.find(ds, n), M.find(ds, n)) == True{} : Bool}
  {D1.moved.ok(t, rs, M.find(ds, n), mv.dep(Up.known(k, only, rs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), n)) == True{} : Bool}

def mv.model_known(k, t, rs, only, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, wk, self):
  match k:
    case False{}:
      self
    case True{}:
      mv.model_pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), t, rs,
        n, name, entry, bin, hub, hubpa, hubpv, ds, ts, wk, self)

# The upgrade's refusals. A pin whose fate refuses makes the walk refuse,
# since a refusal ahead of the rest wins and its reason is never empty
# (`Up.halt.why`), and a walk that refuses stops the upgrade, which stops the
# lock.

# LAW: the dependency `M.find` answers from a repository has the name asked for
law mv.find_pick_named:
  for b: Bool
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for e: {String.eq(hn, n) == b : Bool}
  for g: {M.source.is_git(M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))))
    == True{} : Bool}
  for ih: {M.source.is_git(M.source.dep(M.find(tl, n))) == True{} : Bool}
    -> {M.dep.name(M.find(tl, n)) == n : String}
  {M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))) == n : String}

def mv.find_pick_named(b, n, hn, _hh, _he, _src, _tl, e, g, ih):
  match b:
    case True{}:
      Str.string_eq_true(hn, n, e)
    case False{}:
      ih(g)

law mv.find_named:
  for +ds: List<&2, M.Dep>
  for +n: String
  for g: {M.source.is_git(M.source.dep(M.find(ds, n))) == True{} : Bool}
  {M.dep.name(M.find(ds, n)) == n : String}

def mv.find_named(ds, n, g):
  match ds:
    case []:
      Eq.bit.absurd(&2, {"" == n : String}, g)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.find_pick_named(String.eq(hn, n), n, hn, hh, he, src, tl, {==}, g,
            p => mv.find_named(tl, n, p))

# LAW: and so does the one a ledger that was read answers
law mv.dep_named:
  for r: M.Read
  for +n: String
  for g: {M.source.is_git(M.source.dep(M.dep(r, n))) == True{} : Bool}
  {M.dep.name(M.dep(r, n)) == n : String}

def mv.dep_named(r, n, g):
  match r:
    case M.Bad{_why}:
      Eq.bit.absurd(&2, {"" == n : String}, g)
    case M.Good{m}:
      match m:
        case M.Manifest{_name, _entry, _bin, _hub, _hubpa, _hubpv, +ds, _ts}:
          mv.find_named(ds, n, g)

# LAW: a tip that is another commit, which the remote says does not descend
# from the pin, is refused
law mv.tip_off:
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for moved: {String.eq(rev, tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{url, rev, tip}) == Up.Asc{False{}} : Up.Asc}
  {mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend))) == True{} : Bool}

def mv.tip_off(rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br, moved, off):
  Equal.trans(Bool,
    mv.halts(Up.dep.same(String.eq(rev, tip), rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    mv.halts(Up.dep.same(False{}, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    True{},
    Equal.cong(Bool, Bool, s => mv.halts(Up.dep.same(s, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
      String.eq(rev, tip), False{}, moved),
    Equal.cong(Up.Asc, Bool, a => mv.halts(Up.dep.onward(a, rs, hub,
      mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
      Up.onward(rs, Up.Above{url, rev, tip}), Up.Asc{False{}}, off))

# LAW: a walk with no dependencies has no refusal to carry, so none of them
# refused
law mv.halts_nil:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for hl: {mv.halts(Up.dep.one(U.aim(s, M.Hub{""}), rs, only, hub, M.Dep{"", "", "", M.Hub{""}}))
    == True{} : Bool}
  {String.is_empty(mv.bad(Up.deps.walk(rs, only, hub, []))) == False{} : Bool}

def mv.halts_nil(s, _rs, _only, _hub, hl):
  match s:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hl)
    case False{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hl)

# LAW: a fate that refuses, in front of the rest, makes the walk refuse
law mv.join_bad:
  for f: Up.Fate
  for rest: Up.Deps
  for hl: {mv.halts(f) == True{} : Bool}
  {String.is_empty(mv.bad(Up.deps.join(f, rest))) == False{} : Bool}

def mv.join_bad(f, rest, hl):
  match f rest:
    case Up.Became{_d, _, _, _, _, _, _} Up.Deps{_ds, _ss, _es, _any, _sy2, _tr2, _asks, bad}:
      Eq.bit.absurd(&2, {String.is_empty(bad) == False{} : Bool}, hl)
    case Up.Waits{_more} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, bad}:
      Eq.bit.absurd(&2, {String.is_empty(bad) == False{} : Bool}, hl)
    case Up.Halts{why} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, _bad}:
      M1.mv.halt_ne(why)

# LAW: and a walk that refused behind any fate still refuses
law mv.join_keeps:
  for f: Up.Fate
  for rest: Up.Deps
  for ih: {String.is_empty(mv.bad(rest)) == False{} : Bool}
  {String.is_empty(mv.bad(Up.deps.join(f, rest))) == False{} : Bool}

def mv.join_keeps(f, rest, ih):
  match f rest:
    case Up.Became{_d, _, _, _, _, _, _} Up.Deps{_ds, _ss, _es, _any, _sy2, _tr2, _asks, _bad}:
      ih
    case Up.Waits{_more} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, _bad}:
      ih
    case Up.Halts{why} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, _bad}:
      M1.mv.halt_ne(why)

# LAW: one step of the walk
law mv.halts_step:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for hl: {mv.halts(Up.dep.one(U.aim(U.chosen(only,
    M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))),
    M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))), rs, only, hub,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))) == True{} : Bool}
  for ih: {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(tl, n))),
    M.source.dep(M.find(tl, n))), rs, only, hub, M.find(tl, n))) == True{} : Bool}
    -> {String.is_empty(mv.bad(Up.deps.walk(rs, only, hub, tl))) == False{} : Bool}
  {String.is_empty(mv.bad(Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub,
    M.Dep{hn, hh, he, src}), Up.deps.walk(rs, only, hub, tl)))) == False{} : Bool}

def mv.halts_step(b, rs, only, hub, _n, hn, hh, he, src, tl, hl, ih):
  match b:
    case True{}:
      mv.join_bad(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), hl)
    case False{}:
      mv.join_keeps(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), ih(hl))

# LAW: the walk refuses when the named dependency's fate does
law mv.walk_halts:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +ds: List<&2, M.Dep>
  for hl: {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(ds, n))),
    M.source.dep(M.find(ds, n))), rs, only, hub, M.find(ds, n))) == True{} : Bool}
  {String.is_empty(mv.bad(Up.deps.walk(rs, only, hub, ds))) == False{} : Bool}

def mv.walk_halts(rs, only, hub, n, ds, hl):
  match ds:
    case []:
      mv.halts_nil(U.chosen(only, ""), rs, only, hub, hl)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.halts_step(String.eq(hn, n), rs, only, hub, n, hn, hh, he, src, tl, hl,
            p => mv.walk_halts(rs, only, hub, n, tl, p))

# LAW: a walk that refuses stops the upgrade
law mv.pins_stop:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for wb: {String.is_empty(mv.bad(dd)) == False{} : Bool}
  {mv.stops(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})) == True{} : Bool}

def mv.pins_stop(dd, tt, rs, name, entry, bin, hub, hubpa, hubpv, ds, ts, wb):
  match dd tt:
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, +dasks, SNil{}} Up.Tools{+tts, +tm, +tsy, +tasks, +tbad}:
      Eq.bit.absurd2(&2, {mv.stops(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, ""},
        Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}))
        == True{} : Bool}, wb)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SCon{_c, _cs}} Up.Tools{_tts, _tm, _tsy, _tasks, _tbad}:
      {==}

# LAW: and so does a `--package` that names nothing
law mv.known_stop:
  for k: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for wb: {String.is_empty(mv.bad(Up.deps.walk(rs, only, M.hub.or(hub), ds))) == False{} : Bool}
  {mv.stops(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})) == True{} : Bool}

def mv.known_stop(k, rs, only, name, entry, bin, hub, hubpa, hubpv, ds, ts, wb):
  match k:
    case False{}:
      {==}
    case True{}:
      mv.pins_stop(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), rs, name,
        entry, bin, hub, hubpa, hubpv, ds, ts, wb)

# LAW: an upgrade that stops is a lock that refuses
law mv.refuses_of:
  for nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for st: {mv.stops(nx) == True{} : Bool}
  {P.refuses.doc(P.decide(W.inputs.of(nx, listing, replies))) == True{} : Bool}

def mv.refuses_of(nx, listing, replies, st):
  match nx:
    case Up.Next{+model, +read, SNil{}, +asks, +trees, +vends, +says, +edits, +found, +drops, +swaps}:
      Eq.bit.absurd(&2, {P.refuses.doc(P.decide(W.inputs.of(Up.Next{model, read, "", asks, trees,
        vends, says, edits, found, drops, swaps}, listing, replies))) == True{} : Bool}, st)
    case Up.Next{_model, _read, SCon{_c, _cs}, _asks, _trees, _vends, _says, _edits, _found, _drops, _swaps}:
      {==}

# LAW: a lock refuses when the named dependency's fate under `--upgrade` does
law mv.refuses_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  for +n: String
  for g: {M.source.is_git(M.source.dep(M.dep(r, n))) == True{} : Bool}
  for hl: {mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.dep(r, n))),
    M.source.dep(M.dep(r, n))), rs, only, M.hub_of(r), M.dep(r, n))) == True{} : Bool}
  {P.refuses.doc(P.decide(W.inputs.of(Up.next(only, r, rs), listing, replies))) == True{} : Bool}

def mv.refuses_top(r, only, rs, listing, replies, n, g, hl):
  match r:
    case M.Bad{+why}:
      Eq.bit.absurd(&2, {P.refuses.doc(P.decide(W.inputs.of(Up.next(only, M.Bad{why}, rs), listing,
        replies))) == True{} : Bool}, g)
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +hubpa, +hubpv, +ds, +ts}:
          mv.refuses_of(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}}, rs), listing,
            replies, mv.known_stop(Bool.or(U.known(only, ds), M.tool.known(only, ts)), rs, only,
              name, entry, bin, hub, hubpa, hubpv, ds, ts, mv.walk_halts(rs, only, M.hub.or(hub), n, ds, hl)))

# The upgrade reaches the tip. When the lock does not refuse, every pin it
# asked about is at the commit the remote named: moved there, which marks the
# upgrade as having moved a pin, so the ledger it writes is the walk's; or
# there already.

# a fate reaches `tip`: the pin it leaves is at it, and either the fate
# moved it or the old pin was at it already
def mv.live(fate: Up.Fate, +tip: String, +old: M.Dep) -> Bool:
  match fate:
    case Up.Became{d, _o, _n, _p, m, _s, _t}:
      Bool.and(String.eq(M.source.rev(M.source.dep(d)), tip),
        Bool.or(m, String.eq(M.source.rev(M.source.dep(old)), tip)))
    case Up.Waits{_asks}:
      True{}
    case Up.Halts{_why}:
      True{}

# the walk reaches `tip` for the dependency named `n`: it refuses, or still
# asks, or the dependency it leaves under that name is at `tip`, and either a
# pin moved or the old pin was at `tip` already
def mv.walk_live(+tip: String, dd: Up.Deps, +old: M.Dep, +n: String) -> Bool:
  Up.Deps{ds, _ss, _es, m, _sy, _tr, asks, bad} = dd
  Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
    Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
      Bool.or(m, String.eq(M.source.rev(M.source.dep(old)), tip)))))

# LAW: a fate that reaches the tip, in front of the rest, still does
law mv.live_or:
  for x: Bool
  for m: Bool
  for +any: Bool
  for +c: Bool
  for lv: {Bool.and(x, Bool.or(m, c)) == True{} : Bool}
  {Bool.and(x, Bool.or(Bool.or(m, any), c)) == True{} : Bool}

def mv.live_or(x, m, any, c, lv):
  match x m:
    case False{} _:
      lv
    case True{} True{}:
      {==}
    case True{} False{}:
      M1.mv.or_r(any, c, lv)

# LAW: and one behind another pin that moved or not
law mv.live_keep:
  for a: Bool
  for b: Bool
  for x: Bool
  for m: Bool
  for +any: Bool
  for +c: Bool
  for ih: {Bool.or(a, Bool.or(b, Bool.and(x, Bool.or(any, c)))) == True{} : Bool}
  {Bool.or(a, Bool.or(b, Bool.and(x, Bool.or(Bool.or(m, any), c)))) == True{} : Bool}

def mv.live_keep(a, b, x, m, _any, _c, ih):
  match a b x m:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} False{} _:
      ih
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      ih

# LAW: a pin moved to the tip, once the hub has not objected
law mv.live_hub:
  for hb: Up.Hubbed
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +hash: String
  for +tip: String
  for +br: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  {mv.live(Up.dep.hub(hb, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), hash, tip, root2,
    nar2, man, srcs, br), tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_hub(
  hb,
  _hn,
  _hh,
  _he,
  _url,
  _rev,
  _tag,
  _root,
  _nar,
  _vend,
  _hash,
  tip,
  _br,
  _root2,
  _nar2,
  _man,
  _srcs
):
  match hb:
    case Up.Clear{}:
      Equal.cong(Bool, Bool, x => Bool.and(x, True{}), String.eq(tip, tip), True{},
        Eq.string_eq_self(tip))
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved to the tip, once its checkout is in
law mv.live_adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +br: String
  {mv.live(Up.dep.advance(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, br),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_adv(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, br):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      mv.live_hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), hn, hh, he, url, rev, tag, root,
        nar, vend, Up.hash.of(man), tip, br, root2, nar2, man, srcs)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: a tip that is another commit, once ancestry is in
law mv.live_onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  {mv.live(Up.dep.onward(a, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_onward(a, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, _tg, br):
  match a:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          mv.live_adv(Up.checkout(rs, Up.Tree{url, tip, he}), rs, hub, hn, hh, he, url, rev, tag,
            root, nar, vend, tip, br)
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the pin's own commit, kept when its checkout agrees
law mv.live_agree:
  for g: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +seen: String
  for e: {String.eq(rev, tip) == True{} : Bool}
  {mv.live(Up.dep.verdict(U.judge(True{}, True{}, g, tip, tg), rs, hub,
    mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, "", seen),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_agree(
  g,
  _rs,
  _hub,
  _hn,
  _hh,
  _he,
  _url,
  rev,
  _tag,
  _root,
  _nar,
  _vend,
  tip,
  _tg,
  _seen,
  e
):
  match g:
    case True{}:
      Equal.cong(Bool, Bool, x => Bool.and(x, x), String.eq(rev, tip), True{}, e)
    case False{}:
      {==}

# LAW: the pin's own commit, once its checkout is in
law mv.live_kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for e: {String.eq(rev, tip) == True{} : Bool}
  {mv.live(Up.dep.kept(co, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_kept(co, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, e):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      mv.live_agree(U.agree(hh, Up.hash.kept(hh, man), nar, nar2, root, root2), rs, hub, hn, hh, he, url,
        rev, tag, root, nar, vend, tip, tg, Up.hash.kept(hh, man), e)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: the tip against the pin
law mv.live_same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for e: {String.eq(rev, tip) == s : Bool}
  {mv.live(Up.dep.same(s, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_same(s, rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br, e):
  match s:
    case True{}:
      mv.live_kept(Up.checkout(rs, Up.Tree{url, rev, he}), rs, hub, hn, hh, he, url, rev, tag, root,
        nar, vend, tip, tg, e)
    case False{}:
      mv.live_onward(Up.onward(rs, Up.Above{url, rev, tip}), rs, hub, hn, hh, he, url, rev, tag,
        root, nar, vend, tip, tg, br)

# LAW: a pin reaches the tip the remote named
law mv.live_tip:
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  {mv.live(Up.dep.tip(Up.At{tip, tg, br}, rs, hub, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)),
    tip, mv.git(hn, hh, he, url, rev, tag, root, nar, vend)) == True{} : Bool}

def mv.live_tip(rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg, br):
  mv.live_same(String.eq(rev, tip), rs, hub, hn, hh, he, url, rev, tag, root, nar, vend, tip, tg,
    br, {==})

# LAW: a walk over no dependencies reaches the tip exactly when the blank pin
# does
law mv.live_nil:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +tip: String
  for lv: {mv.live(Up.dep.one(U.aim(s, M.Hub{""}), rs, only, hub, M.Dep{"", "", "", M.Hub{""}}), tip,
    M.Dep{"", "", "", M.Hub{""}}) == True{} : Bool}
  {mv.walk_live(tip, Up.deps.walk(rs, only, hub, []), M.Dep{"", "", "", M.Hub{""}}, n) == True{} : Bool}

def mv.live_nil(s, _rs, _only, _hub, _n, _tip, lv):
  match s:
    case True{}:
      lv
    case False{}:
      lv

# LAW: the named dependency's fate in front of the rest
law mv.live_hit:
  for f: Up.Fate
  for rest: Up.Deps
  for +n: String
  for +tip: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for e: {String.eq(hn, n) == True{} : Bool}
  for lv: {mv.live(f, tip, M.Dep{hn, hh, he, src}) == True{} : Bool}
  for fn: {M1.mv.fine(f, hn) == (hn, True{}) : String & Bool}
  {mv.walk_live(tip, Up.deps.join(f, rest), M.Dep{hn, hh, he, src}, n) == True{} : Bool}

def mv.live_hit(f, rest, n, tip, hn, _hh, _he, src, e, lv, fn):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, +m, _, _} Up.Deps{+ds, _, _, +any, _, _, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
          dn, hn, Equal.cong(String & Bool, String, p => M1.mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(dsrc), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(M.source.dep(
                M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))))),
            String.eq(hn, n), True{}, e),
          M1.mv.or_r(Bool.not(String.is_empty(bad)),
            Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(dsrc), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip)))),
            M1.mv.or_r(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(dsrc), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(src), tip))),
              mv.live_or(String.eq(M.source.rev(dsrc), tip), m, any,
                String.eq(M.source.rev(src), tip), lv)))))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(src), tip))))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => M1.mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      M1.mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, _bad}:
      M1.mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(src), tip)))),
        M1.mv.halt_not(why))

# LAW: another dependency's fate in front of the rest
law mv.live_miss:
  for f: Up.Fate
  for rest: Up.Deps
  for +n: String
  for +tip: String
  for +hn: String
  for +old: M.Dep
  for e: {String.eq(hn, n) == False{} : Bool}
  for fn: {M1.mv.fine(f, hn) == (hn, True{}) : String & Bool}
  for ih: {mv.walk_live(tip, rest, old, n) == True{} : Bool}
  {mv.walk_live(tip, Up.deps.join(f, rest), old, n) == True{} : Bool}

def mv.live_miss(f, rest, n, tip, hn, old, e, fn, ih):
  match f rest:
    case Up.Became{M.Dep{+dn, +dh, +de, +dsrc}, _, _, _, +m, _, _} Up.Deps{+ds, _, _, +any, _, _, +asks, +bad}:
      Equal.trans(Bool,
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(dn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
        Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(
            M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
            Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
        True{},
        Equal.cong(String, Bool,
          x => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(x, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
          dn, hn, Equal.cong(String & Bool, String, p => M1.mv.fst(p), (dn, True{}), (hn, True{}), fn)),
        Equal.trans(Bool,
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(
              M.find.pick(String.eq(hn, n), M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
          Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
            Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
              Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
          True{},
          Equal.cong(Bool, Bool,
            y => Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
              Bool.and(String.eq(M.source.rev(M.source.dep(
                M.find.pick(y, M.Dep{dn, dh, de, dsrc}, M.find(ds, n)))), tip),
                Bool.or(Bool.or(m, any), String.eq(M.source.rev(M.source.dep(old)), tip))))),
            String.eq(hn, n), False{}, e),
          mv.live_keep(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks)),
            String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip), m, any,
            String.eq(M.source.rev(M.source.dep(old)), tip), ih)))
    case Up.Waits{[]} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, +bad}:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(M.source.dep(old)), tip))))) == True{} : Bool},
        Equal.cong(String & Bool, Bool, p => M1.mv.snd(p), (hn, False{}), (hn, True{}), fn))
    case Up.Waits{_m <> _ms} Up.Deps{_ds, _ss, _es, _any, _sy, _tr, _asks, +bad}:
      M1.mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, +any, _sy, _tr, +asks, _bad}:
      M1.mv.or_l(Bool.not(String.is_empty(Up.halt.why(why))),
        Bool.or(Bool.not(List.is_empty(&2, Up.Ask, asks)),
          Bool.and(String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip),
            Bool.or(any, String.eq(M.source.rev(M.source.dep(old)), tip)))),
        M1.mv.halt_not(why))

# LAW: one step of the walk
law mv.live_step:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +tip: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tl: List<&2, M.Dep>
  for e: {String.eq(hn, n) == b : Bool}
  for lv: {mv.live(Up.dep.one(U.aim(U.chosen(only,
    M.dep.name(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))),
    M.source.dep(M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)))), rs, only, hub,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))), tip,
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n))) == True{} : Bool}
  for ih: {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(tl, n))),
    M.source.dep(M.find(tl, n))), rs, only, hub, M.find(tl, n)), tip, M.find(tl, n))
    == True{} : Bool}
    -> {mv.walk_live(tip, Up.deps.walk(rs, only, hub, tl), M.find(tl, n), n) == True{} : Bool}
  {mv.walk_live(tip, Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub,
    M.Dep{hn, hh, he, src}), Up.deps.walk(rs, only, hub, tl)),
    M.find.pick(b, M.Dep{hn, hh, he, src}, M.find(tl, n)), n) == True{} : Bool}

def mv.live_step(b, rs, only, hub, n, tip, hn, hh, he, src, tl, e, lv, ih):
  match b:
    case True{}:
      mv.live_hit(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), n, tip, hn, hh, he, src, e, lv,
        M1.mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}))
    case False{}:
      mv.live_miss(Up.dep.one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}),
        Up.deps.walk(rs, only, hub, tl), n, tip, hn, M.find(tl, n), e,
        M1.mv.fine_one(U.aim(U.chosen(only, hn), src), rs, only, hub, M.Dep{hn, hh, he, src}), ih(lv))

# LAW: the walk reaches the tip when the named dependency's fate does
law mv.walk_reaches:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +n: String
  for +tip: String
  for +ds: List<&2, M.Dep>
  for lv: {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.find(ds, n))),
    M.source.dep(M.find(ds, n))), rs, only, hub, M.find(ds, n)), tip, M.find(ds, n))
    == True{} : Bool}
  {mv.walk_live(tip, Up.deps.walk(rs, only, hub, ds), M.find(ds, n), n) == True{} : Bool}

def mv.walk_reaches(rs, only, hub, n, tip, ds, lv):
  match ds:
    case []:
      mv.live_nil(U.chosen(only, ""), rs, only, hub, n, tip, lv)
    case +h <> +tl:
      match h:
        case M.Dep{+hn, +hh, +he, +src}:
          mv.live_step(String.eq(hn, n), rs, only, hub, n, tip, hn, hh, he, src, tl, {==}, lv,
            p => mv.walk_reaches(rs, only, hub, n, tip, tl, p))

# LAW: the model, once it is known whether any pin moved
law mv.reach_moved:
  for dm: Bool
  for tm: Bool
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Cli>
  for wk: {Bool.and(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
    Bool.or(dm, String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(M.dep(Up.model.next(Bool.or(dm, tm),
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
      ts}), n))),
    tip) == True{} : Bool}

def mv.reach_moved(dm, tm, tip, n, _name, _entry, _bin, _hub, _hubpa, _hubpv, ds, _ts, dds, _tts, wk):
  match dm tm:
    case True{} _:
      Eq.and.left(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip), True{}, wk)
    case False{} True{}:
      Eq.and.left(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
        String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip), wk)
    case False{} False{}:
      Eq.and.right(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
        String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip), wk)

# LAW: the model, once the sources are known
law mv.reach_srcs:
  for srcs: Up.Srcs
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +ig: String
  for wk: {Bool.and(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
    Bool.or(dm, String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip))) == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), n))), tip)
    == True{} : Bool}

def mv.reach_srcs(
  srcs,
  tip,
  n,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  _ss,
  _es,
  dm,
  _dsy,
  _dtr,
  tts,
  tm,
  _tsy,
  _ig,
  wk,
  se
):
  match srcs:
    case Up.Srcs{_fs}:
      mv.reach_moved(dm, tm, tip, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, tts, wk)
    case Up.SrcsWait{_ask}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        se)
    case Up.SrcsNo{+why}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        M1.mv.halt_clash(why, se))

# LAW: the model, once `.gitignore` is known
law mv.reach_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for wk: {Bool.and(String.eq(M.source.rev(M.source.dep(M.find(dds, n))), tip),
    Bool.or(dm, String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip))) == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.got.ignore(said, srcs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), n))), tip)
    == True{} : Bool}

def mv.reach_ignore(
  said,
  srcs,
  tip,
  n,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  ss,
  es,
  dm,
  dsy,
  dtr,
  tts,
  tm,
  tsy,
  wk,
  se
):
  match said:
    case Up.Said{+ig}:
      mv.reach_srcs(srcs, tip, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dm, dsy, dtr, tts, tm,
        tsy, ig, wk, se)
    case Up.Unsaid{+why}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        M1.mv.halt_clash(why, se))
    case Up.Unasked{_ask}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool},
        se)

# LAW: the model, once the pins are answered or refused
law mv.reach_pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for wk: {mv.walk_live(tip, dd, M.find(ds, n), n) == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})))
    == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.pins(dd, tt, rs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), n))), tip) == True{} : Bool}

def mv.reach_pins(dd, tt, rs, tip, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, wk, se):
  match dd tt:
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SCon{_c, _cs}} Up.Tools{_tts, _tm, _tsy, _tasks, _tbad}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _dasks, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SCon{_c, _cs}}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, _a <> _as, SNil{}} Up.Tools{_tts, _tm, _tsy, _tasks, SNil{}}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{_dds, _ss, _es, _dm, _dsy, _dtr, [], SNil{}} Up.Tools{_tts, _tm, _tsy, _a <> _as, SNil{}}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      mv.reach_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), tip, n, name, entry,
        bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dm, dsy, dtr, tts, tm, tsy, wk, se)

# LAW: the model, once `--package` is known to name something
law mv.reach_known:
  for k: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +tip: String
  for +n: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for wk: {mv.walk_live(tip, Up.deps.walk(rs, only, M.hub.or(hub), ds), M.find(ds, n), n)
    == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts})))
    == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.known(k, only, rs,
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), n))), tip) == True{} : Bool}

def mv.reach_known(k, rs, only, tip, n, name, entry, bin, hub, hubpa, hubpv, ds, ts, wk, se):
  match k:
    case False{}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(M.find(ds, n))), tip) == True{} : Bool}, se)
    case True{}:
      mv.reach_pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), rs, tip,
        n, name, entry, bin, hub, hubpa, hubpv, ds, ts, wk, se)

# LAW: in any ledger an upgrade reads, a pin whose fate reaches the tip is at
# it in the model, when the upgrade does not stop
law mv.reach_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +tip: String
  for g: {M.source.is_git(M.source.dep(M.dep(r, n))) == True{} : Bool}
  for lv: {mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(M.dep(r, n))),
    M.source.dep(M.dep(r, n))), rs, only, M.hub_of(r), M.dep(r, n)), tip, M.dep(r, n))
    == True{} : Bool}
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  {String.eq(M.source.rev(M.source.dep(mv.dep(Up.next(only, r, rs), n))), tip) == True{} : Bool}

def mv.reach_top(r, only, rs, n, tip, g, lv, se):
  match r:
    case M.Bad{+why}:
      Eq.bit.absurd(&2, {String.eq(M.source.rev(M.source.dep(mv.dep(Up.next(only, M.Bad{why}, rs), n))),
        tip) == True{} : Bool}, g)
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +hubpa, +hubpv, +ds, +ts}:
          mv.reach_known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), rs, only, tip, n, name,
            entry, bin, hub, hubpa, hubpv, ds, ts, mv.walk_reaches(rs, only, M.hub.or(hub), n, tip, ds, lv), se)
