# proofs of laws/WorkspaceDoctorPerMember.bend
import Base
import ../src/lock/plan.bend as P
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/doctor.bend as Doc
import ../laws/DoctorWritesNothing.bend as L1
import ../laws/WorkspaceDoctorPerMember.bend as Laws
import ./lemmas/DoctorOnlySays.bend as M1

# ---------------------------------------------------------------------------
# `ez doctor` over a workspace

def Laws.doc_alone(_world):
  {==}

def Laws.doc_judges_joint(_mm, _text, _fs):
  {==}

def Laws.doc_lines(_why, _text, _fs, _world):
  {==}

def Laws.doc_member_file(hd, tl, dirs, at, text, fs, eu):
  %Equal.sym(Bool, Doc.under(WWorkspace.segs.text(hd <> tl), at), True{}, eu)
    : {Doc.own.put(_, W.Source{at, text}, Doc.own.files(hd <> tl, dirs, fs))
      == W.Source{at, text} <> Doc.own.files(hd <> tl, dirs, fs) : List<&2, W.Source>}
  {==}

def Laws.doc_other_file(hd, tl, dirs, at, text, fs, eu):
  %Equal.sym(Bool, Doc.under(WWorkspace.segs.text(hd <> tl), at), False{}, eu)
    : {Doc.own.put(_, W.Source{at, text}, Doc.own.files(hd <> tl, dirs, fs))
      == Doc.own.files(hd <> tl, dirs, fs) : List<&2, W.Source>}
  {==}

def Laws.doc_root_file(dirs, at, text, fs, eu):
  %Equal.sym(Bool, Doc.under.any(dirs, at), False{}, eu)
    : {Doc.own.put(Bool.not(_), W.Source{at, text}, Doc.own.files([], dirs, fs))
      == W.Source{at, text} <> Doc.own.files([], dirs, fs) : List<&2, W.Source>}
  {==}

def Laws.doc_member_drift(_dir, _mm, _dirs, _nvs, _fs):
  {==}

def Laws.doc_drift_lines(_place, _hs, _ln, _ls):
  {==}

def Laws.doc_member_moved(_path, _name, held, root, now, en):
  %Equal.sym(Bool, String.eq(now, held), False{}, en)
    : {Bool.pick(List<&2, DP.Note>, _, [], [DP.Note{True{}, Doc.moved.line(root, now, held)}])
      == [DP.Note{True{}, Doc.moved.line(root, now, held)}] : List<&2, DP.Note>}
  {==}

def Laws.doc_member_same(_path, _name, held, root, now, en):
  %Equal.sym(Bool, String.eq(now, held), True{}, en)
    : {Bool.pick(List<&2, DP.Note>, _, [], [DP.Note{True{}, Doc.moved.line(root, now, held)}])
      == [] : List<&2, DP.Note>}
  {==}

def Laws.doc_member_walks(_dir, _nn, _ee, _bb, _hh, _pa, _pv, _ds, _ts, _files, _locked):
  {==}

def Laws.doc_fails_on_problem(why, text, fs, world, ew):
  %Equal.sym(Bool, DP.wrong(Doc.notes(why, text, fs, world)), True{}, ew)
    : {DP.refuses.plan(P.Plan{DP.says(Doc.notes(why, text, fs, world)), DP.outcome.of(_)}) == True{} : Bool}
  {==}

def Laws.doc_passes_when_fine(why, text, fs, world, ew):
  %Equal.sym(Bool, DP.wrong(Doc.notes(why, text, fs, world)), False{}, ew)
    : {DP.refuses.plan(P.Plan{DP.says(Doc.notes(why, text, fs, world)), DP.outcome.of(_)}) == False{} : Bool}
  {==}

def Laws.doc_writes_nothing(back, world):
  match back:
    case Doc.Alone{}:
      L1.doctor_writes_nothing(world)
    case Doc.Back{+text, +fs, +why}:
      M1.says_quiet(Doc.notes(why, text, fs, world))
