# proofs of laws/WorkspaceFetchChecksMembers.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/lock/world.bend as W
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/WorkspaceFetchChecksMembers.bend as Laws

# ---------------------------------------------------------------------------
# a workspace member's package

def Laws.fetch_member_asks_tree(_path, _entry, _here, _hub, _hash):
  {==}

def Laws.fetch_member_walks(rs, path, entry, fs, _here, _hub, hash, ls, eh):
  %Equal.sym(F.Heard, F.heard(rs, F.Tree{hash, entry}), F.Heard{F.Seen{W.Listed{ls}}}, eh)
    : {FP.part.member(_, fs, path, entry, hash) == FP.member.walked(K.of(entry, FP.files.of(ls)), fs, path, hash)
      : FP.Part}
  {==}

def Laws.fetch_member_same(hash, _root, wfs, _sums, fs, path):
  %Equal.sym(Bool, String.eq(hash, hash), True{}, Eq.string_eq_self(hash))
    : {FP.member.same(_, hash, wfs, fs, path, hash) == FP.Got{FP.cand(fs, "", wfs)} : FP.Part}
  {==}

def Laws.fetch_member_moved(now, _root, wfs, _sums, fs, path, hash, en):
  %Equal.sym(Bool, String.eq(now, hash), False{}, en)
    : {FP.member.same(_, now, wfs, fs, path, hash)
      == FP.No{"ez: workspace member " ++ path ++ " is " ++ now ++ " in the committed files, and the lock records " ++
        hash ++ "; run ez lock"} : FP.Part}
  {==}

def Laws.fetch_member_stops(_fs, _hash, _why, _vs):
  {==}
