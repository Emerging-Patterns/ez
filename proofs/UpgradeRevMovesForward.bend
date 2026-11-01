# proofs of laws/UpgradeRevMovesForward.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/upgrade.bend as U
import ../src/git/git.bend as Git
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../laws/UpgradeRevMovesForward.bend as Laws
import ../laws/defs/LockInputs.bend as D1
import ./lemmas/PlanEffectFacts.bend as M1
import ./lemmas/UpgradeMoves.bend as M2

# LAW: a pin by its commit alone is from a repository
law mv.bare_git:
  for +d: M.Dep
  for bare: {Laws.rev_only(d) == True{} : Bool}
  {M.source.is_git(M.source.dep(d)) == True{} : Bool}

def mv.bare_git(d, bare):
  match d:
    case M.Dep{_hn, _hh, _he, src}:
      match src:
        case M.Hub{hv}:
          bare
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          {==}
        case M.Member{mp, mn}:
          bare

# One pin's fate from what it was asked. A pin by its commit alone follows the
# default branch when it is asked about, and one through a tag its tag; one
# that is not asked about is held.

# LAW: a pin by its commit alone, asked about or not
law mv.fwd_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +root: String
  for +nar: String
  for +vend: Bool
  {M2.mv.ok(Up.dep.one(U.aim(s, M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), Up.forward(rs, url), rs,
    M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}

def mv.fwd_sel(s, rs, _only, hub, hn, hh, he, url, rev, root, nar, vend):
  match s:
    case False{}:
      M2.mv.self(Up.forward(rs, url), rs, hn, hh, he, url, rev, "", root, nar, vend)
    case True{}:
      M2.mv.ok_tip(Up.forward(rs, url), rs, hub, hn, hh, he, url, rev, "", root, nar, vend)

# LAW: a pin by its commit alone moves only along the default branch
law mv.fwd_one:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for bare: {Laws.rev_only(h) == True{} : Bool}
  {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    Up.forward(rs, M.source.url(M.source.dep(h))), rs, h) == True{} : Bool}

def mv.fwd_one(rs, only, hub, h, bare):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}}), Up.forward(rs, ""), rs, M.Dep{hn, hh, he, M.Hub{hv}})
            == True{} : Bool}, bare)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              mv.fwd_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, root, nar, vend)
            case SCon{+c, +ct}:
              Eq.bit.absurd(&2, {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), Up.forward(rs, url), rs,
                M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}, bare)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.ok(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}}), Up.forward(rs, ""), rs, M.Dep{hn, hh, he, M.Member{mp, mn}})
            == True{} : Bool}, bare)

# LAW: a pin by its commit alone, in any ledger an upgrade reads
law mv.fwd_top:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +bare: {Laws.rev_only(M.dep(r, n)) == True{} : Bool}
  {D1.moved.ok(Up.forward(rs, M.source.url(M.source.dep(M.dep(r, n)))), rs, M.dep(r, n),
    M2.mv.dep(Up.next(only, r, rs), n)) == True{} : Bool}

def mv.fwd_top(r, only, rs, n, bare):
  match r:
    case M.Bad{_why}:
      bare
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +hubpa, +hubpv, +ds, +ts}:
          M2.mv.model_known(Bool.or(U.known(only, ds), M.tool.known(only, ts)),
            Up.forward(rs, M.source.url(M.source.dep(M.find(ds, n)))), rs, only, n, name, entry,
            bin, hub, hubpa, hubpv, ds, ts,
            M2.mv.walk_ok(Up.forward(rs, M.source.url(M.source.dep(M.find(ds, n)))), rs, only,
              M.hub.or(hub), n, ds, mv.fwd_one(rs, only, M.hub.or(hub), M.find(ds, n), bare)),
            M2.mv.self_dep(Up.forward(rs, M.source.url(M.source.dep(M.find(ds, n)))), rs,
              M.find(ds, n), mv.bare_git(M.find(ds, n), bare)))

# A plain lock leaves ez.toml's model as it is; an upgrade leaves what the
# walk decided, which is sound for the named dependency.
def Laws.upgrade_forward_moves_onward(w, n, bare):
  match w:
    case W.World{args, +ledger, _listing, _replies, +ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              M2.mv.self_dep(Up.forward(ups, M.source.url(M.source.dep(M.dep(W.parsed(ledger), n)))),
                ups, M.dep(W.parsed(ledger), n), mv.bare_git(M.dep(W.parsed(ledger), n), bare))
            case True{}:
              mv.fwd_top(W.parsed(ledger), only, ups, n, bare)

# LAW: a pin by its commit alone that is asked about, whose default branch
# tip is another commit not descended from it, is refused
law mv.fwd_off_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for head: {Up.forward(rs, url) == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(rev, tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{url, rev, tip}) == Up.Asc{False{}} : Up.Asc}
  {M2.mv.halts(Up.dep.one(U.aim(s, M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend))) == True{} : Bool}

def mv.fwd_off_sel(
  s,
  rs,
  _only,
  hub,
  hn,
  hh,
  he,
  url,
  rev,
  root,
  nar,
  vend,
  tip,
  tg,
  br,
  sel,
  head,
  moved,
  off
):
  match s:
    case False{}:
      sel
    case True{}:
      Equal.trans(Bool,
        M2.mv.halts(Up.dep.tip(Up.forward(rs, url), rs, hub,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend))),
        M2.mv.halts(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend))),
        True{},
        Equal.cong(Up.Tip, Bool, x => M2.mv.halts(Up.dep.tip(x, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend))),
          Up.forward(rs, url), Up.At{tip, tg, br}, head),
        M2.mv.tip_off(rs, hub, hn, hh, he, url, rev, "", root, nar, vend, tip, tg, br, moved, off))

law mv.fwd_off:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for bare: {Laws.rev_only(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for head: {Up.forward(rs, M.source.url(M.source.dep(h))) == Up.At{tip, tg, br} : Up.Tip}
  for moved: {String.eq(M.source.rev(M.source.dep(h)), tip) == False{} : Bool}
  for off: {Up.onward(rs, Up.Above{M.source.url(M.source.dep(h)), M.source.rev(M.source.dep(h)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h))
    == True{} : Bool}

def mv.fwd_off(rs, only, hub, h, tip, tg, br, bare, sel, head, moved, off):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}})) == True{} : Bool}, bare)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              mv.fwd_off_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, root, nar,
                vend, tip, tg, br, sel, head, moved, off)
            case SCon{+c, +ct}:
              Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend))) == True{} : Bool}, bare)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.halts(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}})) == True{} : Bool}, bare)

# `--package` names the dependency, so it is the one asked about
def Laws.upgrade_forward_refuses_off(w, n, tip, tag, branch, up, bare, sel, head, moved, off):
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
                mv.bare_git(M.dep(W.parsed(ledger), n), bare),
                mv.fwd_off(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                  tag, branch, bare,
                  Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                    U.chosen(only, n), True{},
                    Equal.cong(String, Bool, x => U.chosen(only, x),
                      M.dep.name(M.dep(W.parsed(ledger), n)), n,
                      M2.mv.dep_named(W.parsed(ledger), n, mv.bare_git(M.dep(W.parsed(ledger), n), bare))),
                    sel),
                  head, moved, off))

# LAW: a pin by its commit alone that is asked about reaches its default
# branch tip
law mv.fwd_live_sel:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +rev: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +tip: String
  for +tg: String
  for +br: String
  for sel: {s == True{} : Bool}
  for head: {Up.forward(rs, url) == Up.At{tip, tg, br} : Up.Tip}
  {M2.mv.live(Up.dep.one(U.aim(s, M.Git{url, rev, "", root, nar, vend}), rs, only, hub,
    M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
    M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}

def mv.fwd_live_sel(s, rs, only, hub, hn, hh, he, url, rev, root, nar, vend, tip, tg, br, sel, head):
  match s:
    case False{}:
      Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(False{}, M.Git{url, rev, "", root, nar, vend}), rs,
        only, hub, M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
        M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)) == True{} : Bool}, sel)
    case True{}:
      Equal.trans(Bool,
        M2.mv.live(Up.dep.tip(Up.forward(rs, url), rs, hub,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)),
        M2.mv.live(Up.dep.tip(Up.At{tip, tg, br}, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)),
        True{},
        Equal.cong(Up.Tip, Bool, x => M2.mv.live(Up.dep.tip(x, rs, hub,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)), tip,
          M2.mv.git(hn, hh, he, url, rev, "", root, nar, vend)),
          Up.forward(rs, url), Up.At{tip, tg, br}, head),
        M2.mv.live_tip(rs, hub, hn, hh, he, url, rev, "", root, nar, vend, tip, tg, br))

law mv.fwd_live:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  for +tip: String
  for +tg: String
  for +br: String
  for bare: {Laws.rev_only(h) == True{} : Bool}
  for sel: {U.chosen(only, M.dep.name(h)) == True{} : Bool}
  for head: {Up.forward(rs, M.source.url(M.source.dep(h))) == Up.At{tip, tg, br} : Up.Tip}
  {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
    tip, h) == True{} : Bool}

def mv.fwd_live(rs, only, hub, h, tip, tg, br, bare, sel, head):
  match h:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, hn), M.Hub{hv}), rs, only, hub,
            M.Dep{hn, hh, he, M.Hub{hv}}), tip, M.Dep{hn, hh, he, M.Hub{hv}}) == True{} : Bool}, bare)
        case M.Git{+url, +rev, tag, +root, +nar, +vend}:
          match tag:
            case SNil{}:
              mv.fwd_live_sel(U.chosen(only, hn), rs, only, hub, hn, hh, he, url, rev, root, nar,
                vend, tip, tg, br, sel, head)
            case SCon{+c, +ct}:
              Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, hn),
                M.Git{url, rev, SCon{c, ct}, root, nar, vend}), rs, only, hub,
                M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)), tip,
                M2.mv.git(hn, hh, he, url, rev, SCon{c, ct}, root, nar, vend)) == True{} : Bool}, bare)
        case M.Member{mp, mn}:
          Eq.bit.absurd(&2, {M2.mv.live(Up.dep.one(U.aim(U.chosen(only, hn), M.Member{mp, mn}), rs, only, hub,
            M.Dep{hn, hh, he, M.Member{mp, mn}}), tip, M.Dep{hn, hh, he, M.Member{mp, mn}}) == True{} : Bool}, bare)

def Laws.upgrade_forward_reaches_tip(w, n, tip, tag, branch, up, bare, sel, head, ok):
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
                  mv.bare_git(M.dep(W.parsed(ledger), n), bare),
                  mv.fwd_live(ups, only, M.hub_of(W.parsed(ledger)), M.dep(W.parsed(ledger), n), tip,
                    tag, branch, bare,
                    Equal.trans(Bool, U.chosen(only, M.dep.name(M.dep(W.parsed(ledger), n))),
                      U.chosen(only, n), True{},
                      Equal.cong(String, Bool, x => U.chosen(only, x),
                        M.dep.name(M.dep(W.parsed(ledger), n)), n,
                        M2.mv.dep_named(W.parsed(ledger), n, mv.bare_git(M.dep(W.parsed(ledger), n), bare))),
                      sel),
                    head),
                  M1.mv.stop_empty(Up.next(only, W.parsed(ledger), ups), listing, replies, ok)))

# The default branch tip. HEAD's row is found by comparing its name, and its
# first field is taken only when it is a commit, so the premise on each
# comparison is rewritten to the arm it picks. A commit is forty characters,
# so it is never the empty answer that passes to the next row.

def Laws.tip_of_head(rev, rest, e):
  match rev:
    case SNil{}:
      Eq.bit.absurd2(&2, {Git.tip.rev(Git.Row{"", "HEAD"} <> rest) == "" : String}, e)
    case SCon{+c, +t}:
      %e : {Git.tip.step(String.is_empty(Git.tip.rev.hex(_, SCon{c, t})),
        Git.tip.rev.hex(_, SCon{c, t}), _u => Git.tip.rev(rest)) == SCon{c, t} : String}
      {==}

def Laws.tip_skips_other(rev, _name, rest, e):
  %e : {Git.tip.step(String.is_empty(Git.tip.rev.pick(_, Git.is_rev(rev), rev)),
    Git.tip.rev.pick(_, Git.is_rev(rev), rev), _u => Git.tip.rev(rest)) == Git.tip.rev(rest)
    : String}
  {==}

def Laws.tip_skips_symref(rev, rest, e):
  %e : {Git.tip.step(String.is_empty(Git.tip.rev.hex(_, rev)), Git.tip.rev.hex(_, rev),
    _u => Git.tip.rev(rest)) == Git.tip.rev(rest) : String}
  {==}
