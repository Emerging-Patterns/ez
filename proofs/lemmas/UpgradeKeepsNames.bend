# an upgrade keeps each dependency's name, and the one a name finds
import Base
import ../../src/check/str.bend as Str
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/upgrade.bend as U
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A

# One dependency's fate keeps its name. Law vocabulary for the walk below.

# the name a fate leaves in the ledger, or `x` when it leaves none
def fate.name(f: Up.Fate, x: String) -> String:
  match f:
    case Up.Became{d, _old, _new, _prev, _moved, _says, _trees}:
      M.dep.name(d)
    case Up.Waits{_asks}:
      x
    case Up.Halts{_why}:
      x

# LAW: a dependency retargeted keeps its name
law retarget_name:
  for dep: M.Dep
  for rev: String
  for hash: String
  for root: String
  for nar: String
  {M.dep.name(U.retarget(dep, rev, hash, root, nar)) == M.dep.name(dep) : String}

def retarget_name(dep, _rev, _hash, _root, _nar):
  match dep:
    case M.Dep{n, h, e, s}:
      match s:
        case M.Hub{hv}:
          {==}
        case M.Git{url, r, tag, rt, nr, vend}:
          {==}
        case M.Member{mp, mn}:
          {==}

law moved_name:
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {fate.name(Up.dep.moved(dep, hash, rev, root, nar, manifest, srcs, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def moved_name(dep, hash, rev, root, nar, _manifest, _srcs, _branch):
  retarget_name(dep, rev, hash, root, nar)

law hub_name:
  for hubbed: Up.Hubbed
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {fate.name(Up.dep.hub(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def hub_name(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch):
  match hubbed:
    case Up.Clear{}:
      moved_name(dep, hash, rev, root, nar, manifest, srcs, branch)
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

law advance_name:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +rev: String
  for +branch: String
  {fate.name(Up.dep.advance(co, rs, hub, dep, rev, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def advance_name(co, rs, hub, dep, rev, branch):
  match co:
    case Up.Co{nar, root, +manifest, srcs}:
      hub_name(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(manifest)}), dep, Up.hash.of(manifest),
        rev, root, nar, manifest, srcs, branch)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law verdict_name:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +branch: String
  for +seen: String
  {fate.name(Up.dep.verdict(verdict, rs, hub, dep, tip, branch, seen), M.dep.name(dep))
    == M.dep.name(dep) : String}

def verdict_name(verdict, rs, hub, dep, _tip, branch, _seen):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      advance_name(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)), rev, M.dep.entry(dep)}),
        rs, hub, dep, rev, branch)

law kept_name:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  {fate.name(Up.dep.kept(co, rs, hub, dep, tip, tag), M.dep.name(dep))
    == M.dep.name(dep) : String}

def kept_name(co, rs, hub, dep, tip, tag):
  match co:
    case Up.Co{nar, root, +manifest, _srcs}:
      verdict_name(U.judge(True{}, True{},
        U.agree(M.dep.hash(dep), Up.hash.kept(M.dep.hash(dep), manifest), M.source.nar(M.source.dep(dep)), nar,
          M.source.root(M.source.dep(dep)), root), tip, tag), rs, hub, dep, tip, "",
        Up.hash.kept(M.dep.hash(dep), manifest))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law onward_name:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {fate.name(Up.dep.onward(asc, rs, hub, dep, tip, tag, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def onward_name(asc, rs, hub, dep, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      verdict_name(U.judge(False{}, yes, False{}, tip, tag), rs, hub, dep, tip, branch, "")
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law same_name:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {fate.name(Up.dep.same(same, rs, hub, dep, tip, tag, branch), M.dep.name(dep))
    == M.dep.name(dep) : String}

def same_name(same, rs, hub, dep, tip, tag, branch):
  match same:
    case True{}:
      kept_name(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), M.dep.entry(dep)}), rs, hub, dep, tip, tag)
    case False{}:
      onward_name(Up.onward(rs, Up.Above{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), tip}), rs, hub, dep, tip, tag, branch)

law tip_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  {fate.name(Up.dep.tip(tip, rs, hub, dep), M.dep.name(dep)) == M.dep.name(dep) : String}

def tip_name(tip, rs, hub, dep):
  match tip:
    case Up.At{+rev, tag, branch}:
      same_name(String.eq(M.source.rev(M.source.dep(dep)), rev), rs, hub, dep, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: whatever the upgrade makes of one dependency, what it leaves in the
# ledger has the dependency's name
law one_name:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +dep: M.Dep
  {fate.name(Up.dep.one(aim, rs, only, hub, dep), M.dep.name(dep)) == M.dep.name(dep) : String}

def one_name(aim, rs, _only, hub, dep):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      tip_name(Up.follow(rs, M.source.url(M.source.dep(dep)), ref), rs, hub, dep)
    case U.Forward{}:
      tip_name(Up.forward(rs, M.source.url(M.source.dep(dep))), rs, hub, dep)

# the dependencies a walk leaves
def deps.of(dd: Up.Deps) -> List<&2, M.Dep>:
  Up.Deps{ds, _ss, _es, _m, _sy, _tr, _asks, _bad} = dd
  ds

# LAW: an entry of another name, joined in front of the rest, is passed over
# by a lookup
law join_skip:
  for f: Up.Fate
  for r: Up.Deps
  for +x: String
  for +m: String
  for nf: {fate.name(f, x) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.find(deps.of(Up.deps.join(f, r)), m) == M.find(deps.of(r), m) : M.Dep}

# LAW: a dependency of another name, in front of the rest, is passed over
law skip_find:
  for d: M.Dep
  for +ds: List<&2, M.Dep>
  for +x: String
  for +m: String
  for nf: {M.dep.name(d) == x : String}
  for ne: {String.eq(x, m) == False{} : Bool}
  {M.find(d <> ds, m) == M.find(ds, m) : M.Dep}

def skip_find(d, ds, x, m, nf, ne):
  match d:
    case M.Dep{+dn, +dh, +de, +dsrc}:
      nfs = Equal.sym(String, dn, x, nf)
      %nfs : {M.find.pick(String.eq(_, m), M.Dep{dn, dh, de, dsrc}, M.find(ds, m))
        == M.find(ds, m) : M.Dep}
      nes = Equal.sym(Bool, String.eq(x, m), False{}, ne)
      %nes : {M.find.pick(_, M.Dep{dn, dh, de, dsrc}, M.find(ds, m))
        == M.find(ds, m) : M.Dep}
      {==}

def join_skip(f, r, x, m, nf, ne):
  match f:
    case Up.Became{d, old, new, prev, mv, says, trees}:
      match r:
        case Up.Deps{+ds, ss, es, any, sy, tr, asks, bad}:
          skip_find(d, ds, x, m, nf, ne)
    case Up.Waits{more}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}
    case Up.Halts{why}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          {==}

# LAW: an entry that is held, joined in front of the rest, is the one a lookup
# of its name finds
law held_find:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +hs: M.Source
  for r: Up.Deps
  for +m: String
  for e: {String.eq(hn, m) == True{} : Bool}
  for h: {aim == U.Hold{} : U.Aim}
  {M.find(deps.of(Up.deps.join(Up.dep.one(aim, rs, only, hub, M.Dep{hn, hh, he, hs}), r)), m)
    == M.Dep{hn, hh, he, hs} : M.Dep}

def held_find(aim, rs, only, hub, hn, hh, he, hs, r, m, e, h):
  match r:
    case Up.Deps{+ds, +ss, +es, +any, +sy, +tr, +asks, +bad}:
      hsym = Equal.sym(U.Aim, aim, U.Hold{}, h)
      %hsym : {M.find(deps.of(Up.deps.join(Up.dep.one(_, rs, only, hub, M.Dep{hn, hh, he, hs}),
        Up.Deps{ds, ss, es, any, sy, tr, asks, bad})), m) == M.Dep{hn, hh, he, hs} : M.Dep}
      es2 = Equal.sym(Bool, String.eq(hn, m), True{}, e)
      %es2 : {M.find.pick(_, M.Dep{hn, hh, he, hs}, M.find(ds, m)) == M.Dep{hn, hh, he, hs} : M.Dep}
      {==}

# LAW: one dependency of the walk. Its name either is the one looked up, and
# then it is held and found as it was, or it is not, and the lookup goes on to
# the rest, which the walk leaves as it found it.
law find_walk.hit:
  for hit: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +hs: M.Source
  for +t: List<&2, M.Dep>
  for +m: String
  for +e: {String.eq(hn, m) == hit : Bool}
  for pre: {U.aim(U.chosen(only, m),
    M.source.dep(M.find.pick(hit, M.Dep{hn, hh, he, hs}, M.find(t, m)))) == U.Hold{} : U.Aim}
  for ih: {U.aim(U.chosen(only, m), M.source.dep(M.find(t, m))) == U.Hold{} : U.Aim}
    -> {M.find(deps.of(Up.deps.walk(rs, only, hub, t)), m) == M.find(t, m) : M.Dep}
  {M.find(deps.of(Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), hs), rs, only, hub,
    M.Dep{hn, hh, he, hs}), Up.deps.walk(rs, only, hub, t))), m)
    == M.find.pick(hit, M.Dep{hn, hh, he, hs}, M.find(t, m)) : M.Dep}

def find_walk.hit(hit, rs, only, hub, hn, hh, he, hs, t, m, e, pre, ih):
  match hit:
    case True{}:
      held_find(U.aim(U.chosen(only, hn), hs), rs, only, hub, hn, hh, he, hs,
        Up.deps.walk(rs, only, hub, t), m, e,
        Equal.trans(U.Aim, U.aim(U.chosen(only, hn), hs), U.aim(U.chosen(only, m), hs), U.Hold{},
          Equal.cong(String, U.Aim, x => U.aim(U.chosen(only, x), hs), hn, m,
            Str.string_eq_true(hn, m, e)),
          pre))
    case False{}:
      Equal.trans(M.Dep,
        M.find(deps.of(Up.deps.join(Up.dep.one(U.aim(U.chosen(only, hn), hs), rs, only, hub,
          M.Dep{hn, hh, he, hs}), Up.deps.walk(rs, only, hub, t))), m),
        M.find(deps.of(Up.deps.walk(rs, only, hub, t)), m),
        M.find(t, m),
        join_skip(Up.dep.one(U.aim(U.chosen(only, hn), hs), rs, only, hub, M.Dep{hn, hh, he, hs}),
          Up.deps.walk(rs, only, hub, t), hn, m,
          one_name(U.aim(U.chosen(only, hn), hs), rs, only, hub, M.Dep{hn, hh, he, hs}), e),
        ih(pre))

# LAW: the walk leaves the dependency a name finds as it was, when that
# dependency is held
law find_walk:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for ds: List<&2, M.Dep>
  for +m: String
  for pre: {U.aim(U.chosen(only, m), M.source.dep(M.find(ds, m))) == U.Hold{} : U.Aim}
  {M.find(deps.of(Up.deps.walk(rs, only, hub, ds)), m) == M.find(ds, m) : M.Dep}

def find_walk(rs, only, hub, ds, m, pre):
  match ds:
    case []:
      {==}
    case h <> +t:
      match h:
        case M.Dep{+hn, +hh, +he, +hs}:
          find_walk.hit(String.eq(hn, m), rs, only, hub, hn, hh, he, hs, t, m, {==}, pre,
            p => find_walk(rs, only, hub, t, m, p))

# The pipeline. `Up.next` walks the dependencies and the tools, and then
# either stops, with ez.toml's model as it was, or renders the model with the
# walked lists in place of the old ones. So anything read off the model that
# the walked lists leave as it was, the upgrade leaves as it was. Each lemma
# is one def of the pipeline, with the value it branches on as a parameter.

# the tools a walk leaves
def tools.of(tt: Up.Tools) -> List<&2, M.Tool>:
  Up.Tools{ts, _m, _sy, _asks, _bad} = tt
  ts

# LAW: the model an upgrade renders, or the old one
law model_kept:
  for A: Type
  for f: M.Read -> A
  for moved: Bool
  for +next: M.Manifest
  for +old: M.Manifest
  for pre: {f(M.Good{next}) == f(M.Good{old}) : A}
  {f(Up.model.next(moved, next, old)) == f(M.Good{old}) : A}

def model_kept(_A, _f, moved, _next, _old, pre):
  match moved:
    case True{}:
      pre
    case False{}:
      {==}

law done_kept:
  for A: Type
  for f: M.Read -> A
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ignore: String
  for fs: List<&2, Up.Found>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.done(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt, ignore, fs)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def done_kept(A, f, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, _ignore, _fs, pre):
  match dd:
    case Up.Deps{+ds, ss, es, dm, dsy, dtr, das, dbad}:
      match tt:
        case Up.Tools{+ts, tm, tsy, tas, tbad}:
          model_kept(A, f, Bool.or(dm, tm), M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts},
            M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, pre)

law srcs_kept:
  for A: Type
  for f: M.Read -> A
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ignore: String
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt, ignore)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def srcs_kept(A, f, srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, ignore, pre):
  match srcs:
    case Up.Srcs{fs}:
      done_kept(A, f, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, ignore, fs, pre)
    case Up.SrcsWait{_ask}:
      {==}
    case Up.SrcsNo{_why}:
      {==}

law ignore_kept:
  for A: Type
  for f: M.Read -> A
  for said: Up.Said
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for dd: Up.Deps
  for tt: Up.Tools
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.got.ignore(said, srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def ignore_kept(A, f, said, srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, pre):
  match said:
    case Up.Said{ignore}:
      srcs_kept(A, f, srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, ignore, pre)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law asks_kept:
  for A: Type
  for f: M.Read -> A
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for tt: Up.Tools
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.pins.asks(asks, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def asks_kept(A, f, asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, pre):
  match asks:
    case []:
      ignore_kept(A, f, Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd)), rs),
        pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, pre)
    case _h <> _t:
      {==}

law bad_kept:
  for A: Type
  for f: M.Read -> A
  for clean: Bool
  for bad: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for +dd: Up.Deps
  for tt: Up.Tools
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.pins.bad(clean, bad, asks, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def bad_kept(A, f, clean, _bad, asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, pre):
  match clean:
    case True{}:
      asks_kept(A, f, asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, pre)
    case False{}:
      {==}

law pins_kept:
  for A: Type
  for f: M.Read -> A
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, deps.of(dd), tools.of(tt)}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.pins(dd, tt, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots})))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def pins_kept(A, f, dd, tt, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, pre):
  match dd:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad}:
      match tt:
        case Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
          bad_kept(A, f, Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            List.append(&2, Up.Ask, das, tas), rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots,
            Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}, pre)

law next_kept.known:
  for A: Type
  for f: M.Read -> A
  for ok: Bool
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv,
    deps.of(Up.deps.walk(rs, only, M.hub.or(hb), ods)), tools.of(Up.tools.walk(rs, only, ots))}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.known(ok, only, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots})))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def next_kept.known(A, f, ok, only, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, pre):
  match ok:
    case False{}:
      {==}
    case True{}:
      pins_kept(A, f, Up.deps.walk(rs, only, M.hub.or(hb), ods), Up.tools.walk(rs, only, ots), rs,
        pn, pe, pb, hb, hbpa, hbpv, ods, ots, pre)

# LAW: whatever `--package` named and whatever the remote said, the model an
# upgrade leaves reads, through `f`, as ez.toml's does, once the walked lists
# read so
law next_kept:
  for A: Type
  for f: M.Read -> A
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Tool>
  for pre: {f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv,
    deps.of(Up.deps.walk(rs, only, M.hub.or(hb), ods)), tools.of(Up.tools.walk(rs, only, ots))}})
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}
  {f(Up.next.model(Up.next(only, M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, rs)))
    == f(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}) : A}

def next_kept(A, f, only, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, pre):
  next_kept.known(A, f, Bool.or(U.known(only, ods), M.tool.known(only, ots)), only, rs,
    pn, pe, pb, hb, hbpa, hbpv, ods, ots, pre)
