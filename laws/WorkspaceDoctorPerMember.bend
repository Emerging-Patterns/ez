# In a workspace, `ez doctor` reports, for each member, every hash its
# import lines name that its own ledger does not and every dependency of its
# ledger that no import line of its own names, judges the root lock as
# laws/DoctorJudgesLock.bend does over every member's ledger, and reports a
# member whose hash is not the one the lock records. It exits 1 when it
# reports any.
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/moved.bend as Mv
import ../src/ws/doctor.bend as Doc

# ---------------------------------------------------------------------------
# `ez doctor` over a workspace (laws/WorkspaceDoctorPerMember.bend)

# LAW: for a project of its own, `ez doctor` makes the plan it always made
law doc_alone:
  for +world: DW.World
  {Doc.plan(Doc.Alone{}, world) == DP.plan(world) : P.Plan}

# LAW: at a workspace root it judges the joint ledger, the text `ez lock`
# plans the root lock from, so the ledger, the lock, the library and the lock
# check (laws/DoctorJudgesLock.bend) are judged over every member's ledger
law doc_judges_joint:
  for +mm: M.Manifest
  for +text: String
  for +fs: List<&2, J.Found>
  {Doc.joint(J.Joint{mm}, text, fs) == Doc.Doctored{J.joint.text(J.Joint{mm}, None{}), Doc.Back{text, fs, ""}}
    : Doc.Doctored}

# LAW: and says the doctor's own lines on it, with every member's report in
# place of the one drift report
law doc_lines:
  for +why: String
  for +text: String
  for +fs: List<&2, J.Found>
  for +world: DW.World
  {Doc.plan(Doc.Back{text, fs, why}, world)
    == DP.plan.notes(List.append(&2, DP.Note,
      DP.head.notes(DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
        DW.replies(world), DP.checked(world)),
      Doc.tail(why, text, fs, world))) : P.Plan}

# LAW: a member's report is over its own files, the ones under its directory
law doc_member_file:
  for +hd: String
  for +tl: List<&2, String>
  for +dirs: List<&2, List<&2, String>>
  for +at: String
  for text: String
  for +fs: List<&2, W.Source>
  for eu: {Doc.under(WWorkspace.segs.text(hd <> tl), at) == True{} : Bool}
  {Doc.own.files(hd <> tl, dirs, W.Source{at, text} <> fs) == W.Source{at, text} <> Doc.own.files(hd <> tl, dirs, fs)
    : List<&2, W.Source>}

# LAW: and not over another's
law doc_other_file:
  for +hd: String
  for +tl: List<&2, String>
  for +dirs: List<&2, List<&2, String>>
  for +at: String
  for text: String
  for +fs: List<&2, W.Source>
  for eu: {Doc.under(WWorkspace.segs.text(hd <> tl), at) == False{} : Bool}
  {Doc.own.files(hd <> tl, dirs, W.Source{at, text} <> fs) == Doc.own.files(hd <> tl, dirs, fs)
    : List<&2, W.Source>}

# LAW: the root's report is over the files under no member's directory
law doc_root_file:
  for +dirs: List<&2, List<&2, String>>
  for +at: String
  for text: String
  for +fs: List<&2, W.Source>
  for eu: {Doc.under.any(dirs, at) == False{} : Bool}
  {Doc.own.files([], dirs, W.Source{at, text} <> fs) == W.Source{at, text} <> Doc.own.files([], dirs, fs)
    : List<&2, W.Source>}

# LAW: a member's report holds, in both directions, every hash its own
# import lines name that its own ledger does not, and every dependency of
# its ledger that none of them names (`DP.unrecorded`, `DP.unused`,
# laws/DoctorReportsDrift.bend), each `workspace = true` section resolved to
# the member's package, and a member imported by its published name counting
# as named
law doc_member_drift:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +dirs: List<&2, List<&2, String>>
  for +nvs: List<&2, String>
  for +fs: List<&2, W.Source>
  {Doc.member.drift(J.Member{dir, mm}, dirs, nvs, fs)
    == Doc.drift.notes(J.ledger.at(dir), DP.imports(Doc.own.files(dir, dirs, fs)),
      List.append(&2, String,
        DP.unrecorded(DP.missing(DP.imports(Doc.own.files(dir, dirs, fs)),
          List.append(&2, String, DP.pinned(J.deps.of(mm)), nvs))),
        DP.unused(J.deps.of(mm), DP.imports(Doc.own.files(dir, dirs, fs))))) : List<&2, DP.Note>}

# LAW: every line of a member's report is a problem, said for the member
law doc_drift_lines:
  for +place: String
  for hs: List<&2, String>
  for +ln: String
  for +ls: List<&2, String>
  {Doc.drift.notes(place, hs, ln <> ls) == DP.flag(Doc.at.lines(place, ln <> ls)) : List<&2, DP.Note>}

# LAW: a member whose package walks, from its entry over the committed files,
# to a hash the lock does not record for it at its directory is reported, as
# a problem
law doc_member_moved:
  for path: String
  for name: String
  for +held: String
  for +root: String
  for +now: String
  for en: {String.eq(now, held) == False{} : Bool}
  {Doc.moved.at(Some{Mv.Held{path, name, held}}, root, now) == [DP.Note{True{}, Doc.moved.line(root, now, held)}]
    : List<&2, DP.Note>}

# LAW: and one at the hash the lock records is not
law doc_member_same:
  for path: String
  for name: String
  for +held: String
  for +root: String
  for +now: String
  for en: {String.eq(now, held) == True{} : Bool}
  {Doc.moved.at(Some{Mv.Held{path, name, held}}, root, now) == [] : List<&2, DP.Note>}

# LAW: the walk is from the member's own entry over the committed files
law doc_member_walks:
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  for +files: List<&2, K.Source>
  for +locked: List<&2, Mv.Held>
  {Doc.member.moved(J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}, files, locked)
    == Doc.moved.walked(K.of(J.entry.at(dir, ee), files), locked) : List<&2, DP.Note>}

# LAW: `ez doctor` at a workspace root fails, so it exits 1, when any line it
# says is a problem
law doc_fails_on_problem:
  for +why: String
  for +text: String
  for +fs: List<&2, J.Found>
  for +world: DW.World
  for ew: {DP.wrong(Doc.notes(why, text, fs, world)) == True{} : Bool}
  {DP.refuses.plan(Doc.plan(Doc.Back{text, fs, why}, world)) == True{} : Bool}

# LAW: and passes when none is
law doc_passes_when_fine:
  for +why: String
  for +text: String
  for +fs: List<&2, J.Found>
  for +world: DW.World
  for ew: {DP.wrong(Doc.notes(why, text, fs, world)) == False{} : Bool}
  {DP.refuses.plan(Doc.plan(Doc.Back{text, fs, why}, world)) == False{} : Bool}

# LAW: and it writes nothing
law doc_writes_nothing:
  for +back: Doc.Back
  for +world: DW.World
  {P.writes(Doc.plan(back, world)) == False{} : Bool}
