# proofs of laws/UpgradeHoldsHub.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/manifest.bend as M
import ../src/ledger/upgrade.bend as U
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../laws/UpgradeHoldsHub.bend as Laws
import ./lemmas/UpgradeKeepsNames.bend as M1

# LAW: and a hub entry is held whether it is chosen or not
law hub_holds:
  for sel: Bool
  for s: M.Source
  for e: {M.source.is_git(s) == False{} : Bool}
  {U.aim(sel, s) == U.Hold{} : U.Aim}

# LAW: a hub source is held, chosen or not, by its name or by its hash
law hub_source_holds:
  for sel: Bool
  for hv: String
  {U.aim(sel, M.Hub{hv}) == U.Hold{} : U.Aim}

def hub_source_holds(sel, _hv):
  match sel:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a workspace member's source is held, chosen or not
law member_source_holds:
  for sel: Bool
  for path: String
  for named: String
  {U.aim(sel, M.Member{path, named}) == U.Hold{} : U.Aim}

def member_source_holds(sel, _path, _named):
  match sel:
    case True{}:
      {==}
    case False{}:
      {==}

def hub_holds(sel, s, e):
  match s:
    case M.Hub{hv}:
      hub_source_holds(sel, hv)
    case M.Git{url, rev, tag, root, nar, vend}:
      Eq.bit.absurd2(&2, {U.aim(sel, M.Git{url, rev, tag, root, nar, vend}) == U.Hold{} : U.Aim}, e)
    case M.Member{path, named}:
      member_source_holds(sel, path, named)

# laws/UpgradeHoldsHub.bend. A hub dependency is held whether `--package`
# chose it or not, so the walk leaves the dependency its name finds as it
# was, and so does the model. A plain lock's model is ez.toml's.

law hub_read:
  for +only: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +n: String
  for pre: {M.source.is_git(M.source.dep(M.dep(r, n))) == False{} : Bool}
  {M.dep(Up.next.model(Up.next(only, r, rs)), n) == M.dep(r, n) : M.Dep}

def hub_read(only, r, rs, n, pre):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{m}:
      match m:
        case M.Manifest{+pn, +pe, +pb, +hb, +hbpa, +hbpv, +ods, +ots}:
          M1.next_kept(M.Dep, x => M.dep(x, n), only, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots,
            M1.find_walk(rs, only, M.hub.or(hb), ods, n,
              hub_holds(U.chosen(only, n), M.source.dep(M.find(ods, n)), pre)))

def Laws.upgrade_holds_hub(w, n, pre):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, +only, +here}:
          match up:
            case False{}:
              {==}
            case True{}:
              hub_read(only, W.parsed(ledger), ups, n, pre)
