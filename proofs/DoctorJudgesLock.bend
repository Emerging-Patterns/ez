# proofs of laws/DoctorJudgesLock.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../laws/DoctorJudgesLock.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

# ---------------------------------------------------------------------------
# laws/DoctorJudgesLock.bend
#
# The lock check's lines stand after the library's and before the drift
# report, so a line the check says is said by doctor (`said_check`), and a
# check line that is a problem fails it (`wrong_check`). What the check says
# is found by rewriting the World's lock, its sources and the lock planner's
# open questions and decision to what each law assumes, after which the check
# is one note computed.

# LAW: one step of the front, with its head decided
law said_left.step:
  for bb: Bool
  for +t: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for +line: String
  for e: {DP.has.step(bb, _u => DP.said.in(DP.says(t), line)) == True{} : Bool}
  for ih: {DP.said.in(DP.says(t), line) == True{} : Bool}
    -> {DP.said.in(DP.says(List.append(&2, DP.Note, t, b)), line) == True{} : Bool}
  {DP.has.step(bb, _u => DP.said.in(DP.says(List.append(&2, DP.Note, t, b)), line)) == True{}
    : Bool}

def said_left.step(bb, _t, _b, _line, e, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: a line said by the first lines is said by all of them
law said_append_left:
  for a: List<&2, DP.Note>
  for +b: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(a), line) == True{} : Bool}
  {DP.said.in(DP.says(List.append(&2, DP.Note, a, b)), line) == True{} : Bool}

def said_append_left(a, b, line, e):
  match a:
    case []:
      Eq.bit.absurd(&2,
        {DP.said.in(DP.says(List.append(&2, DP.Note, [], b)), line) == True{} : Bool}, e)
    case h <> +t:
      match h:
        case DP.Note{_w, +l}:
          said_left.step(String.eq(l, line), t, b, line, e,
            z => said_append_left(t, b, line, z))

# LAW: a line the lock check says is said by doctor
law said_check:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for +line: String
  for e: {DP.said.in(DP.says(cs), line) == True{} : Bool}
  {DP.said.in(DP.says(DP.notes.of(led, got, cc, lib, lock, rs, cs)), line) == True{} : Bool}

def said_check(led, got, cc, lib, lock, rs, cs, line, e):
  said_append_left(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got), line,
    M1.said_append(DP.probes(DP.programs(cc), rs),
      List.append(&2, DP.Note,
        [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
          DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
      line,
      M1.said_append(
        [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
          DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
        line, e)))

# LAW: and a lock check line that is a problem fails doctor
law wrong_check:
  for +led: M.Read
  for +got: DW.Heard
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for e: {DP.wrong(cs) == True{} : Bool}
  {DP.refuses.plan(DP.plan.notes(DP.notes.of(led, got, cc, lib, lock, rs, cs))) == True{} : Bool}

def wrong_check(led, got, cc, lib, lock, rs, cs, e):
  M1.refuses_wrong(DP.notes.of(led, got, cc, lib, lock, rs, cs),
    M1.wrong_append_left(DP.head.notes(led, cc, lib, lock, rs, cs), DP.imports.notes(led, got),
      M1.wrong_append(DP.probes(DP.programs(cc), rs),
        List.append(&2, DP.Note,
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs),
        M1.wrong_append(
          [DP.ledger.note(led), DP.lock.note(DP.deps.count(led), DP.locked.of(lock)),
            DP.lib.note(DP.lib.at(lib), DP.locked.hashes(DP.locked.of(lock)), DP.lock.names(lock), rs)], cs,
          e))))

# LAW: a note alone says its own line
law said_one:
  for +b: Bool
  for +line: String
  {DP.said.in(DP.says([DP.Note{b, line}]), line) == True{} : Bool}

def said_one(_b, line):
  M1.step_hit(String.eq(line, line), _u => DP.said.in(DP.says([]), line),
    Eq.string_eq_self(line))

# LAW: over any World the lock planner asks nothing more of, about packages
# or names, the check's one line is the lock planner's verdict on the text:
# up to date when it decides on that text
law away_fresh:
  for +lw: W.World
  for +t: String
  for o: {[] == P.wants(lw) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(lw) : List<&2, W.Ask>}
  for d: {P.Doc{t} == P.decide(W.inputs(lw)) : P.Doc}
  {[DP.fresh.away(P.wants(lw), lw, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}

def away_fresh(lw, t, o, on, d):
  %o : {[DP.fresh.away(_, lw, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %on : {[DP.fresh.named(_, lw, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %d : {[DP.fresh.doc(_, t)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %Equal.sym(Bool, String.eq(t, t), True{}, Eq.string_eq_self(t))
    : {[DP.fresh.said(_)] == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  {==}

# LAW: and out of date when it decides on another
law away_stale:
  for +lw: W.World
  for +t: String
  for +u: String
  for o: {[] == P.wants(lw) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(lw) : List<&2, W.Ask>}
  for d: {P.Doc{u} == P.decide(W.inputs(lw)) : P.Doc}
  for ne: {False{} == String.eq(u, t) : Bool}
  {[DP.fresh.away(P.wants(lw), lw, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}

def away_stale(lw, t, _u, o, on, d, ne):
  %o : {[DP.fresh.away(_, lw, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %on : {[DP.fresh.named(_, lw, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %d : {[DP.fresh.doc(_, t)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %ne : {[DP.fresh.said(_)] == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  {==}

# LAW: a World the lock planner still asks about a package makes the line a
# problem
law away_asks:
  for +lw: W.World
  for +t: String
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for o: {a <> as == P.wants(lw) : List<&2, W.Ask>}
  {DP.wrong([DP.fresh.away(P.wants(lw), lw, t)]) == True{} : Bool}

def away_asks(lw, t, _a, _as, o):
  %o : {DP.wrong([DP.fresh.away(_, lw, t)]) == True{} : Bool}
  {==}

# LAW: and so does one it still asks about a name
law away_names:
  for +lw: W.World
  for +t: String
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for o: {[] == P.wants(lw) : List<&2, W.Ask>}
  for on: {a <> as == P.wants.names(lw) : List<&2, W.Ask>}
  {DP.wrong([DP.fresh.away(P.wants(lw), lw, t)]) == True{} : Bool}

def away_names(lw, t, _a, _as, o, on):
  %o : {DP.wrong([DP.fresh.away(_, lw, t)]) == True{} : Bool}
  %on : {DP.wrong([DP.fresh.named(_, lw, t)]) == True{} : Bool}
  {==}

def Laws.doctor_passes_fresh_lock(w, t, fs, k, l, o, on, d):
  %k : {DP.fresh.notes(_, w) == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  %l : {DP.fresh.heard(_, w, t) == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}
  away_fresh(DP.relock(w, fs), t, o, on, d)

# LAW: the check's one line, for a lock that differs from the one decided on
law checked_stale:
  for +w: DW.World
  for +t: String
  for +u: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{u} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  for ne: {False{} == String.eq(u, t) : Bool}
  {DP.checked(w) == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}

def checked_stale(w, t, u, fs, k, l, o, on, d, ne):
  %k : {DP.fresh.notes(_, w) == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  %l : {DP.fresh.heard(_, w, t) == [DP.Note{True{}, DP.stale.line()}] : List<&2, DP.Note>}
  away_stale(DP.relock(w, fs), t, u, o, on, d, ne)

def Laws.doctor_says_fresh_lock(w, t, fs, k, l, o, on, d):
  said_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), DP.fresh.line(),
    Equal.trans(Bool, DP.said.in(DP.says(DP.checked(w)), DP.fresh.line()),
      DP.said.in(DP.says([DP.Note{False{}, DP.fresh.line()}]), DP.fresh.line()), True{},
      Equal.cong(List<&2, DP.Note>, Bool, ns => DP.said.in(DP.says(ns), DP.fresh.line()),
        DP.checked(w), [DP.Note{False{}, DP.fresh.line()}],
        Laws.doctor_passes_fresh_lock(w, t, fs, k, l, o, on, d)),
      said_one(False{}, DP.fresh.line())))

def Laws.doctor_reports_stale_lock(w, t, u, fs, k, l, o, on, d, ne):
  said_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), DP.stale.line(),
    Equal.trans(Bool, DP.said.in(DP.says(DP.checked(w)), DP.stale.line()),
      DP.said.in(DP.says([DP.Note{True{}, DP.stale.line()}]), DP.stale.line()), True{},
      Equal.cong(List<&2, DP.Note>, Bool, ns => DP.said.in(DP.says(ns), DP.stale.line()),
        DP.checked(w), [DP.Note{True{}, DP.stale.line()}],
        checked_stale(w, t, u, fs, k, l, o, on, d, ne)),
      said_one(True{}, DP.stale.line())))

def Laws.doctor_stale_lock_fails(w, t, u, fs, k, l, o, on, d, ne):
  wrong_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w),
    Equal.trans(Bool, DP.wrong(DP.checked(w)), DP.wrong([DP.Note{True{}, DP.stale.line()}]), True{},
      Equal.cong(List<&2, DP.Note>, Bool, ns => DP.wrong(ns),
        DP.checked(w), [DP.Note{True{}, DP.stale.line()}],
        checked_stale(w, t, u, fs, k, l, o, on, d, ne)),
      {==}))

# LAW: a lock the lock planner still has questions about is a problem
law checked_away:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {a <> as == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.wrong(DP.checked(w)) == True{} : Bool}

def checked_away(w, t, fs, a, as, k, l, o):
  %k : {DP.wrong(DP.fresh.notes(_, w)) == True{} : Bool}
  %l : {DP.wrong(DP.fresh.heard(_, w, t)) == True{} : Bool}
  away_asks(DP.relock(w, fs), t, a, as, o)

def Laws.doctor_unchecked_lock_fails(w, t, fs, a, as, k, l, o):
  wrong_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w), checked_away(w, t, fs, a, as, k, l, o))

# LAW: a lock the lock planner still asks a name's hash about is a problem
law checked_names_away:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {a <> as == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.wrong(DP.checked(w)) == True{} : Bool}

def checked_names_away(w, t, fs, a, as, k, l, o, on):
  %k : {DP.wrong(DP.fresh.notes(_, w)) == True{} : Bool}
  %l : {DP.wrong(DP.fresh.heard(_, w, t)) == True{} : Bool}
  away_names(DP.relock(w, fs), t, a, as, o, on)

def Laws.doctor_unchecked_names_fail(w, t, fs, a, as, k, l, o, on):
  wrong_check(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}), DW.cc(w),
    DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w),
    checked_names_away(w, t, fs, a, as, k, l, o, on))
