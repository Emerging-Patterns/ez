# ws/doctor: `ez doctor` at a workspace root (EZ-WS-9). The doctor runs at the
# root, as `ez lock` does (ws/hop.bend), on a World whose ledger is the joint
# ledger (ws/joint.bend), so the toolchain, the ledger, the lock, the library
# and the lock check are judged over every member's ledger as the lock is
# made from them. The drift report is each member's own: the hashes its import
# lines name that its ledger does not, and the dependencies of its ledger no
# import line of its own names, with each `workspace = true` section resolved
# to the member's package as the joint ledger resolves it. A member whose
# package walks to a hash the lock does not record for it is reported too.
# Every report that is a problem fails the command (`DP.plan.notes`).
import Base
import ../doctor/plan.bend as DP
import ../doctor/world.bend as DW
import ../lock/plan.bend as P
import ../lock/world.bend as LW
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../pkg/pkg.bend as K
import ../pub/plan.bend as PP
import ./workspace.bend as W
import ./joint.bend as J
import ./moved.bend as Mv

# what the doctor needs beyond its World: nothing, for a project of its own;
# or the root's ledger text, every other ez.toml git lists, and why the joint
# ledger could not be made, "" when it was
type Back is Data:
  Alone{}
  Back{text: String, found: List<&2, J.Found>, why: String}

# the ledger the doctor judges, and what else it needs
type Doctored is Data:
  Doctored{ledger: Maybe<&2, String>, back: Back}

# what the doctor judges at a workspace root: the joint ledger, the same text
# `ez lock` plans the root lock from, or, when it cannot be made, the root's
# own ledger with why
def joint(jj: J.Joint, +text: String, +fs: List<&2, J.Found>) -> Doctored:
  match jj:
    case J.Lone{}:
      Doctored{Some{text}, Alone{}}
    case J.Clash{why}:
      Doctored{Some{text}, Back{text, fs, why}}
    case J.Joint{mm}:
      Doctored{Some{Rend.show(mm)}, Back{text, fs, ""}}

# ---------------------------------------------------------------------------
# each member's own files

# whether a path is under a directory of the root
def under(+dir: String, +at: String) -> Bool:
  String.starts_with(at, dir ++ "/")

# whether a path is under any member's directory
def under.any(dirs: List<&2, List<&2, String>>, +at: String) -> Bool:
  match dirs:
    case []:
      False{}
    case +hd <> tl:
      rest = under.any(tl, at)
      Bool.or(Bool.and(Bool.not(List.is_empty(&2, String, hd)), under(W.segs.text(hd), at)), rest)

# whether a committed file is a member's own: under its directory, or, for
# the root, under no member's
def own.at(dir: List<&2, String>, +dirs: List<&2, List<&2, String>>, +at: String) -> Bool:
  match dir:
    case []:
      Bool.not(under.any(dirs, at))
    case hd <> tl:
      under(W.segs.text(hd <> tl), at)

# a file kept, when it is the member's own
def own.put(hit: Bool, src: LW.Source, rest: List<&2, LW.Source>) -> List<&2, LW.Source>:
  match hit:
    case True{}:
      src <> rest
    case False{}:
      rest

# the committed files that are a member's own
def own.files(
  +dir: List<&2, String>,
  +dirs: List<&2, List<&2, String>>,
  fs: List<&2, LW.Source>
) -> List<&2, LW.Source>:
  match fs:
    case []:
      []
    case LW.Source{+at, text} <> tl:
      rest = own.files(dir, dirs, tl)
      own.put(own.at(dir, dirs, at), LW.Source{at, text}, rest)

# ---------------------------------------------------------------------------
# each member's drift

# every member's directory
def dirs.of(xs: List<&2, J.Member>) -> List<&2, List<&2, String>>:
  match xs:
    case []:
      []
    case J.Member{dir, _mm} <> tl:
      dir <> dirs.of(tl)

# the name a member is imported by, when it publishes under one
def nv.of(named: PP.Named) -> List<&2, String>:
  match named:
    case PP.ByName{nv}:
      [nv]
    case PP.ByHash{}:
      []
    case PP.Unnamed{_why}:
      []

# every name a member is imported by. Such a name is resolved in the
# workspace whether or not a section names it (EZ-WS-6), so no member's
# ledger has to.
def nvs.of(xs: List<&2, J.Member>) -> List<&2, String>:
  match xs:
    case []:
      []
    case hd <> tl:
      List.append(&2, String, nv.of(J.member.naming(hd)), nvs.of(tl))

# both directions of a member's disagreement: a hash its own import lines
# name that its own ledger does not, and a dependency of its ledger none of
# them names
def drift(+hs: List<&2, String>, +ds: List<&2, M.Dep>, +nvs: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, DP.unrecorded(DP.missing(hs, List.append(&2, String, DP.pinned(ds), nvs))),
    DP.unused(ds, hs))

# a member's line, said for the member
def at.lines(+place: String, ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case hd <> tl:
      (place ++ ": " ++ hd) <> at.lines(place, tl)

# a member's report, or the one line that says there is nothing to report
def drift.notes(+place: String, +hs: List<&2, String>, lines: List<&2, String>) -> List<&2, DP.Note>:
  match lines:
    case []:
      [DP.Note{False{}, "imports: " ++ place ++ ": " ++
        DP.plural(List.length(&2, String, hs), "package", "packages") ++ " imported, every one named in it"}]
    case hd <> tl:
      DP.flag(at.lines(place, hd <> tl))

# one member's drift report, over its own files
def member.drift(
  mb: J.Member,
  +dirs: List<&2, List<&2, String>>,
  +nvs: List<&2, String>,
  +fs: List<&2, LW.Source>
) -> List<&2, DP.Note>:
  J.Member{+dir, mm} = mb
  +hs = DP.imports(own.files(dir, dirs, fs))
  drift.notes(J.ledger.at(dir), hs, drift(hs, J.deps.of(mm), nvs))

# ---------------------------------------------------------------------------
# a member against the lock

# how a moved member reads
def moved.line(+root: String, +now: String, +held: String) -> String:
  "workspace: member " ++ root ++ " is " ++ now ++ " in the committed files, and the lock records " ++
    held ++ "; run ez lock"

# a member's walk against what the lock records at its directory, once that
# is looked up
def moved.at(found: Maybe<&2, Mv.Held>, +root: String, +now: String) -> List<&2, DP.Note>:
  match found:
    case None{}:
      []
    case Some{hd}:
      Mv.Held{_path, _name, +held} = hd
      Bool.pick(List<&2, DP.Note>, String.eq(now, held), [], [DP.Note{True{}, moved.line(root, now, held)}])

# a member's walk against the lock
def moved.walked(got: K.Walked, +locked: List<&2, Mv.Held>) -> List<&2, DP.Note>:
  match got:
    case K.Walked{+now, +root, _fs, _sums}:
      moved.at(Mv.at(locked, root), root, now)
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# one member against the lock: its package walked from its entry over the
# committed files, reported when the lock records another hash at its
# directory
def member.moved(mb: J.Member, +files: List<&2, K.Source>, +locked: List<&2, Mv.Held>) -> List<&2, DP.Note>:
  J.Member{+dir, mm} = mb
  M.Manifest{_n, ee, _b, _h, _pa, _pv, _ds, _ts} = mm
  moved.walked(K.of(J.entry.at(dir, ee), files), locked)

# every member's report: its drift, then whether it moved
def members.notes(
  xs: List<&2, J.Member>,
  +dirs: List<&2, List<&2, String>>,
  +nvs: List<&2, String>,
  +fs: List<&2, LW.Source>,
  +locked: List<&2, Mv.Held>
) -> List<&2, DP.Note>:
  match xs:
    case []:
      []
    case +hd <> tl:
      rest = members.notes(tl, dirs, nvs, fs, locked)
      List.append(&2, DP.Note, member.drift(hd, dirs, nvs, fs),
        List.append(&2, DP.Note, member.moved(hd, J.files.of(fs), locked), rest))

# the members' reports, once they were resolved
def resolved.notes(rd: J.Read, +fs: List<&2, LW.Source>, +locked: List<&2, Mv.Held>) -> List<&2, DP.Note>:
  match rd:
    case J.Unread{why}:
      [DP.Note{True{}, "workspace: " ++ why}]
    case J.Read{+xs}:
      members.notes(xs, dirs.of(xs), nvs.of(xs), fs, locked)

# the members' reports over the sources as git listed them
def listing.notes(
  listing: LW.Listing,
  +text: String,
  +found: List<&2, J.Found>,
  +lock: String
) -> List<&2, DP.Note>:
  match listing:
    case LW.Listed{+fs}:
      resolved.notes(J.resolved(text, found, J.files.of(fs)), fs, Mv.locked(lock))
    case LW.Unlisted{_why}:
      [DP.Note{True{}, "imports: git could not list the .bend files it tracks here"}]

# the members' reports, once the sources were asked for
def sources.notes(got: DW.Heard, +text: String, +found: List<&2, J.Found>, +lock: String) -> List<&2, DP.Note>:
  match got:
    case DW.Heard{a}:
      match a:
        case DW.Listed{l}:
          listing.notes(l, text, found, lock)
        case _:
          [DP.Note{True{}, "imports: the sources were not read"}]
    case DW.Open{}:
      [DP.Note{True{}, "imports: the sources were not read"}]

# ---------------------------------------------------------------------------
# the plan

# what the doctor says after the toolchain, the ledger, the lock, the
# library and the lock check: why the joint ledger could not be made, or else
# every member's report
def tail.pick(
  fine: Bool,
  +why: String,
  +text: String,
  +found: List<&2, J.Found>,
  +world: DW.World
) -> List<&2, DP.Note>:
  match fine:
    case True{}:
      sources.notes(DW.heard(DW.replies(world), DW.Sources{}), text, found, DP.lock.text(DW.lock(world)))
    case False{}:
      [DP.Note{True{}, why}]

# and so, once it is known whether the joint ledger was made
def tail(+why: String, +text: String, +found: List<&2, J.Found>, +world: DW.World) -> List<&2, DP.Note>:
  tail.pick(String.is_empty(why), why, text, found, world)

# every line the doctor says at a workspace root
def notes(+why: String, +text: String, +found: List<&2, J.Found>, +world: DW.World) -> List<&2, DP.Note>:
  List.append(&2, DP.Note,
    DP.head.notes(DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
      DW.replies(world), DP.checked(world)),
    tail(why, text, found, world))

# `ez doctor`: for a project of its own, the doctor's plan; at a workspace
# root, the same lines over the joint ledger, with each member's report in
# place of the one drift report
def plan(back: Back, +world: DW.World) -> P.Plan:
  match back:
    case Alone{}:
      DP.plan(world)
    case Back{+text, +found, +why}:
      DP.plan.notes(notes(why, text, found, world))

# the step, once the doctor's own is known: its questions, or this plan
def step.of(st: DP.Step, back: Back, +world: DW.World) -> DP.Step:
  match st:
    case DP.Asking{asks}:
      DP.Asking{asks}
    case DP.Run{_pl}:
      DP.Run{plan(back, world)}

# what the interpreter does next: the doctor asks what it always asks, the
# sources among them, and its plan is this one
def step(back: Back, +world: DW.World) -> DP.Step:
  step.of(DP.step(world), back, world)
