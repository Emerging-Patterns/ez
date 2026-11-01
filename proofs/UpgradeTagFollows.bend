# proofs of laws/UpgradeTagFollows.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/upgrade.bend as U
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../laws/UpgradeTagFollows.bend as Laws
import ../laws/defs/LockInputs.bend as D1
import ./lemmas/PlanEffectFacts.bend as M1
import ./lemmas/UpgradeMoves.bend as M2

# LAW: and so is one through a tag
law mv.named_git:
  for +d: M.Dep
  for named: {Laws.tagged(d) == True{} : Bool}
  {M.source.is_git(M.source.dep(d)) == True{} : Bool}

def mv.named_git(d, named):
  match d:
    case M.Dep{_hn, _hh, _he, src}:
      match src:
        case M.Hub{hv}:
          named
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          {==}
        case M.Member{mp, mn}:
          named

# LAW: a pin through a tag, asked about or not
law mv.fol_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {M2.mv.ok(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), Up.follow(rs, url, SCon{c, ct}),
    rs, M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}

def mv.fol_sel(s, rs, _only, hub, hn, hh, he, url, rev, c, ct, root, nar, vend):
  match s:
    case False{}:
      M2.mv.self(Up.follow(rs, url, SCon{c, ct}), rs, hn, hh, he, url, rev, SCon{c, ct}, root, nar,
        vend)
    case True{}:
      M2.mv.ok_tip(Up.follow(rs, url, SCon{c, ct}), rs, hub, hn, hh, he, url, rev, SCon{c, ct},
        root, nar, vend)

# LAW: a pin through a tag moves only to what the tag names, along its history
law mv.fol_one:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for named: {Laws.tagged(h) == True{} : Bool}
  {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h))), rs, h)
    == True{} : Bool}

def mv.fol_one(rs, only, hub, h, named):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}}), Up.follow(rs, "", ""), rs, M.Dep{hn, hh, he, M.Hub{hv}})
            == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), Up.follow(rs, url, ""), rs,
                M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root, nar,
                vend)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}}), Up.follow(rs, "", ""), rs, M.Dep{hn, hh, he, M.Member{mp, mn}})
            == True{} : Bool}, named)

# LAW: a pin through a tag, in any ledger an upgrade reads
law mv.fol_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +named: {Laws.tagged(M.dep(r, n)) == True{} : Bool}
  {D1.moved.ok(Up.follow(rs, M.source.url(M.source.dep(M.dep(r, n))),
    M.source.tag(M.source.dep(M.dep(r, n)))), rs, M.dep(r, n),
    M2.mv.dep(Up.next(only, r, rs), n)) == True{} : Bool}

def mv.fol_top(r, only, rs, n, named):
  match r:
    case M.Bad{_why}:
      named
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +hubpa, +hubpv, +ds, +ts}:
          M2.mv.model_known(Bool.or(U.known(only, ds), M.tool.known(only, ts)),
            Up.follow(rs, M.source.url(M.source.dep(M.find(ds, n))),
              M.source.tag(M.source.dep(M.find(ds, n)))), rs, only, n, name, entry, bin, hub, hubpa, hubpv, ds, ts,
            M2.mv.walk_ok(Up.follow(rs, M.source.url(M.source.dep(M.find(ds, n))),
              M.source.tag(M.source.dep(M.find(ds, n)))), rs, only, M.hub.or(hub), n, ds,
              mv.fol_one(rs, only, M.hub.or(hub), M.find(ds, n), named)),
            M2.mv.self_dep(Up.follow(rs, M.source.url(M.source.dep(M.find(ds, n))),
              M.source.tag(M.source.dep(M.find(ds, n)))), rs, M.find(ds, n),
              mv.named_git(M.find(ds, n), named)))

def Laws.upgrade_tag_follows(w, n, named):
  match w:
    case W.World{args, +ledger, _listing, _replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              M2.mv.self_dep(Up.follow(ups, M.source.url(M.source.dep(M.dep(W.parsed(ledger), n))),
                M.source.tag(M.source.dep(M.dep(W.parsed(ledger), n)))),
                ups, M.dep(W.parsed(ledger), n), mv.named_git(M.dep(W.parsed(ledger), n), named))
            case True{}:
              mv.fol_top(W.parsed(ledger), only, ups, n, named)

# LAW: the pin's own commit, whose checkout no longer agrees with the pin, is
# refused
law mv.tip_drift:
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
  for +nar2: String
  for +root2: String
  for +man: String
  for +srcs: List<&2, String>
  for same: {String.eq(rev, tip) == True{} : Bool}
  for co: {Up.checkout(rs, Up.Tree{url, rev, he}) == Up.Co{nar2, root2, man, srcs} : Up.Co}
  for drift: {U.agree(hh, Up.hash.kept(hh, man), nar, nar2, root, root2) == False{} : Bool}
  {M2.mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
    M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend))) == True{} : Bool}

def mv.tip_drift(
  rs,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  tag,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  nar2,
  root2,
  man,
  srcs,
  same,
  co,
  drift
):
  Equal.trans(Bool,
    M2.mv.halts(Up.dep.same(String.eq(rev, tip), rs, hub,
      M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    M2.mv.halts(Up.dep.same(True{}, rs, hub,
      M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
    True{},
    Equal.cong(Bool, Bool, s => M2.mv.halts(Up.dep.same(s, rs, hub,
      M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg, br)),
      String.eq(rev, tip), True{}, same),
    Equal.trans(Bool,
      M2.mv.halts(Up.dep.kept(Up.checkout(rs, Up.Tree{url, rev, he}), rs, hub,
        M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg)),
      M2.mv.halts(Up.dep.kept(Up.Co{nar2, root2, man, srcs}, rs, hub,
        M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg)),
      True{},
      Equal.cong(Up.Co, Bool, c => M2.mv.halts(Up.dep.kept(c, rs, hub,
        M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, tg)),
        Up.checkout(rs, Up.Tree{url, rev, he}), Up.Co{nar2, root2, man, srcs}, co),
      Equal.cong(Bool, Bool, g => M2.mv.halts(Up.dep.verdict(U.judge(True{}, True{}, g, tip, tg), rs,
        hub, M2.mv.git(hn, hh, he, url, rev, tag, root, nar, vend), tip, "", Up.hash.kept(hh, man))),
        U.agree(hh, Up.hash.kept(hh, man), nar, nar2, root, root2), False{}, drift)))

# LAW: a pin through a tag that is asked about, whose tag now names another
# commit not descended from it, is refused
law mv.fol_off_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for refs: {Up.follow(rs, url, SCon{c, ct}) == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(rev, tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{url, rev, tip}) == Up.Asc{False{}} : Up.Asc}
  {M2.mv.halts(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))) == True{} : Bool}

def mv.fol_off_sel(
  s,
  rs,
  _only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  c,
  ct,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  sel,
  refs,
  moved,
  off
):
  match s:
    case False{}:
      sel
    case True{}:
      Equal.trans(Bool,
        M2.mv.halts(Up.dep.tip(Up.follow(rs, url, SCon{c, ct}), rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        M2.mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        True{},
        Equal.cong(Up.Tip, Bool, x => M2.mv.halts(Up.dep.tip(x, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
          Up.follow(rs, url, SCon{c, ct}), Up.At{tip, tg, br}, refs),
        M2.mv.tip_off(rs, hub, hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend, tip, tg, br, moved,
          off))

law mv.fol_off:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for named: {Laws.tagged(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for refs: {Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h)))
    == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(M.source.rev(M.source.dep(h)), tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{M.source.url(M.source.dep(h)), M.source.rev(M.source.dep(h)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h))
    == True{} : Bool}

def mv.fol_off(rs, only, hub, h, tip, tg, br, named, sel, refs, moved, off):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}})) == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend))) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_off_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root,
                nar, vend, tip, tg, br, sel, refs, moved, off)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}})) == True{} : Bool}, named)

# LAW: a pin through a tag that is asked about, whose tag still names its
# commit but whose checkout no longer agrees with it, is refused
law mv.fol_drift_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for +nar2: String
  for +root2: String
  for +man: String
  for +srcs: List<&2, String>
  for sel: {s == True{} : Bool}
  for refs: {Up.follow(rs, url, SCon{c, ct}) == Up.At{tip, tg, br} : Up.Tip}
  for same: {String.eq(rev, tip) == True{} : Bool}
  for co: {Up.checkout(rs, Up.Tree{url, rev, he}) == Up.Co{nar2, root2, man, srcs} : Up.Co}
  for drift: {U.agree(hh, Up.hash.kept(hh, man), nar, nar2, root, root2) == False{} : Bool}
  {M2.mv.halts(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))) == True{} : Bool}

def mv.fol_drift_sel(
  s,
  rs,
  _only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  c,
  ct,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  nar2,
  root2,
  man,
  srcs,
  sel,
  refs,
  same,
  co,
  drift
):
  match s:
    case False{}:
      sel
    case True{}:
      Equal.trans(Bool,
        M2.mv.halts(Up.dep.tip(Up.follow(rs, url, SCon{c, ct}), rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        M2.mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
        True{},
        Equal.cong(Up.Tip, Bool, x => M2.mv.halts(Up.dep.tip(x, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))),
          Up.follow(rs, url, SCon{c, ct}), Up.At{tip, tg, br}, refs),
        mv.tip_drift(rs, hub, hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend, tip, tg, br, nar2,
          root2, man, srcs, same, co, drift))

law mv.fol_drift:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for +nar2: String
  for +root2: String
  for +man: String
  for +srcs: List<&2, String>
  for named: {Laws.tagged(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for refs: {Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h)))
    == Up.At{tip, tg, br} : Up.Tip}
  for same: {String.eq(M.source.rev(M.source.dep(h)), tip) == True{} : Bool}
  for co: {Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(h)), M.source.rev(M.source.dep(h)),
    M.dep.entry(h)}) == Up.Co{nar2, root2, man, srcs} : Up.Co}
  for drift: {U.agree(M.dep.hash(h), Up.hash.kept(M.dep.hash(h), man), M.source.nar(M.source.dep(h)), nar2,
    M.source.root(M.source.dep(h)), root2) == False{} : Bool}
  {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h))
    == True{} : Bool}

def mv.fol_drift(
  rs,
  only,
  hub,
  h,
  tip,
  tg,
  br,
  nar2,
  root2,
  man,
  srcs,
  named,
  sel,
  refs,
  same,
  co,
  drift
):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}})) == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend))) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_drift_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root,
                nar, vend, tip, tg, br, nar2, root2, man, srcs, sel, refs, same, co, drift)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}})) == True{} : Bool}, named)

def Laws.upgrade_tag_refuses_off(w, n, tip, tag, branch, up, named, sel, refs, moved, off):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only, +here}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {P.refuses(W.World{W.Args{False{}, only, here}, ledger, listing, replies,
                ups}) == True{} : Bool}, up)
            case True{}:
              M2.mv.refuses_top(W.parsed(ledger), only, ups, listing, replies, n,
                mv.named_git(M.dep(W.parsed(ledger), n), named),
                mv.fol_off(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                  tag, branch, named,
                  Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                    U.chosen(only, n), True{},
                    Equal.cong(String, Bool, x => U.chosen(only, x),
                      M.dep.name(M.dep(W.parsed(ledger), n)), n,
                      M2.mv.dep_named(W.parsed(ledger), n, mv.named_git(M.dep(W.parsed(ledger), n), named))),
                    sel),
                  refs, moved, off))

def Laws.upgrade_tag_refuses_drift(
  w,
  n,
  tip,
  tag,
  branch,
  nar,
  root,
  manifest,
  srcs,
  up,
  named,
  sel,
  refs,
  same,
  co,
  drift
):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only, +here}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {P.refuses(W.World{W.Args{False{}, only, here}, ledger, listing, replies,
                ups}) == True{} : Bool}, up)
            case True{}:
              M2.mv.refuses_top(W.parsed(ledger), only, ups, listing, replies, n,
                mv.named_git(M.dep(W.parsed(ledger), n), named),
                mv.fol_drift(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                  tag, branch, nar, root, manifest, srcs, named,
                  Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                    U.chosen(only, n), True{},
                    Equal.cong(String, Bool, x => U.chosen(only, x),
                      M.dep.name(M.dep(W.parsed(ledger), n)), n,
                      M2.mv.dep_named(W.parsed(ledger), n, mv.named_git(M.dep(W.parsed(ledger), n), named))),
                    sel),
                  refs, same, co, drift))

# LAW: a pin through a tag that is asked about reaches what its tag names
law mv.fol_live_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +c: Char
  for +ct: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for refs: {Up.follow(rs, url, SCon{c, ct}) == Up.At{tip, tg, br} : Up.Tip}
  {M2.mv.live(Up.dep.one(U.aim(s, M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
    M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}

def mv.fol_live_sel(
  s,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  c,
  ct,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  sel,
  refs
):
  match s:
    case False{}:
      Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(False{}, M.Git{url, rev, SCon{c, ct}, root, nar,
        vend}), rs, only, hub, M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
        M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}, sel)
    case True{}:
      Equal.trans(Bool,
        M2.mv.live(Up.dep.tip(Up.follow(rs, url, SCon{c, ct}), rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)),
        M2.mv.live(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)),
        True{},
        Equal.cong(Up.Tip, Bool, x => M2.mv.live(Up.dep.tip(x, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
          M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)),
          Up.follow(rs, url, SCon{c, ct}), Up.At{tip, tg, br}, refs),
        M2.mv.live_tip(rs, hub, hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend, tip, tg, br))

law mv.fol_live:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for named: {Laws.tagged(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for refs: {Up.follow(rs, M.source.url(M.source.dep(h)), M.source.tag(M.source.dep(h)))
    == Up.At{tip, tg, br} : Up.Tip}
  {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    tip, h) == True{} : Bool}

def mv.fol_live(rs, only, hub, h, tip, tg, br, named, sel, refs):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}}), tip, M.Dep{hn, hh, he, M.Hub{hv}}) == True{} : Bool}, named)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
                M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}, named)
            case SCon{+c, +ct}:
              mv.fol_live_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, c, ct, root,
                nar, vend, tip, tg, br, sel, refs)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}}), tip, M.Dep{hn, hh, he, M.Member{mp, mn}}) == True{} : Bool}, named)

def Laws.upgrade_tag_resolves(w, n, tip, tag, branch, up, named, sel, refs, ok):
  match w:
    case W.World{args, +ledger, +listing, +replies, +ups}:
      match args:
        case W.Args{u, +only, +here}:
          match u:
            case False{}:
              Eq.bit.absurd(&2, {M.source.rev(M.source.dep(M.dep(P.ledger.next(W.World{
                W.Args{False{}, only, here}, ledger, listing, replies, ups}), n))) == tip : String}, up)
            case True{}:
              Str.string_eq_true(M.source.rev(M.source.dep(M2.mv.dep(Up.next(only, W.parsed(ledger), ups),
                n))), tip,
                M2.mv.reach_top(W.parsed(ledger), only, ups, n, tip,
                  mv.named_git(M.dep(W.parsed(ledger), n), named),
                  mv.fol_live(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                    tag, branch, named,
                    Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                      U.chosen(only, n), True{},
                      Equal.cong(String, Bool, x => U.chosen(only, x),
                        M.dep.name(M.dep(W.parsed(ledger), n)), n,
                        M2.mv.dep_named(W.parsed(ledger), n, mv.named_git(M.dep(W.parsed(ledger), n), named))),
                      sel),
                    refs),
                  M1.mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok)))
