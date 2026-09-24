# doctor: the laws. The human states them; PROOF.bend must prove them. They
# are stated over the plan `ez doctor` runs (doctor/plan.bend) and the step
# its interpreter takes (`DP.step`), so what they say of the plan is what the
# command does, the interpreter's faithfulness being EZ-TRUST-2.
#
# An import line names a hash when the lock reads it so: `P.roots(fs)` is
# every hub package the header of a tracked `.bend` file outside `.ez/`
# imports, as the package walk scans it, and it is what `ez lock` resolves.
# `DW.sources(w)` is the answer the World holds for the sources, which the
# interpreter asks for whenever the ledger reads.
#
# `DP.relock(w, fs)` is the World doctor puts to the lock planner over the
# sources `fs`: a plain `ez lock` over the ledger's text, tools and all, the
# lock as it is, every tree the World read from BEND_LIB, and every name's
# file it read there. `P.wants` of it is what the lock planner still asks
# about packages, which once doctor has asked everything it can is the
# packages BEND_LIB lacks, `P.wants.names` what it still asks about names,
# which is the names whose files BEND_LIB lacks, and `P.decide` of its inputs
# is the lock `ez lock` would write, or why it would write none.
# `DP.checked(w)` is what doctor says of the lock against it.
import Base
import ./world.bend as DW
import ./plan.bend as DP
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../manifest/manifest.bend as M

# LAW: `ez doctor` writes, lays and removes nothing, whatever it found: its
# plan is lines said and how the command ends, so no source file, ledger,
# lock or tree is touched
# EZ-VEN-4
law doctor_writes_nothing:
  for +w: DW.World
  {P.writes(DP.plan(w)) == False{} : Bool}

# LAW: `ez doctor` ends with the status of its plan's outcome, which is 1
# exactly when it fails the command and 0 when it does not
# EZ-OUT-1
law doctor_exits_as_it_fails:
  for +w: DW.World
  {P.code(DP.plan(w)) == P.status.of(DP.refuses(w)) : U32}

# LAW: every hash an import line names that the ledger's dependencies do not
# is reported, on its own line
# EZ-VEN-5
law doctor_reports_unrecorded:
  for +w: DW.World
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +fs: List<&2, W.Source>
  for +h: String
  for g: {M.Good{M.Manifest{n, e, b, hub, ds, ts}} == DW.read(w) : M.Read}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for i: {DP.has(P.roots(fs), h) == True{} : Bool}
  for u: {False{} == DP.has(DP.pinned(ds), h) : Bool}
  {DP.said(DP.plan(w), DP.unrecorded.line(h)) == True{} : Bool}

# LAW: and every dependency of the ledger that no import line names, by its
# hash or by the name the ledger records it by, is reported, on its own line,
# wherever it stands in the ledger
# EZ-VEN-5
law doctor_reports_unused:
  for +w: DW.World
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +pre: List<&2, M.Dep>
  for +d: M.Dep
  for +post: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +fs: List<&2, W.Source>
  for g: {M.Good{M.Manifest{n, e, b, hub, List.append(&2, M.Dep, pre, d <> post), ts}}
    == DW.read(w) : M.Read}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for u: {False{} == DP.used(DP.imports(fs), d) : Bool}
  {DP.said(DP.plan(w), DP.unused.line(d)) == True{} : Bool}

# LAW: and when the report holds any line, `ez doctor` fails, so it exits 1
# EZ-VEN-5
law doctor_drift_fails:
  for +w: DW.World
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +fs: List<&2, W.Source>
  for +x: String
  for +xs: List<&2, String>
  for g: {M.Good{M.Manifest{n, e, b, hub, ds, ts}} == DW.read(w) : M.Read}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for r: {DP.drift.of(fs, ds) == x <> xs : List<&2, String>}
  {DP.refuses(w) == True{} : Bool}

# LAW: a ledger's `[tools.*]` pins change nothing doctor says or how it ends
# outside the lock check, which compares the lock with the one `ez lock`
# writes and so reads the pins the lock records: two ledgers that differ only
# in their tools make the same plan around the same check, so a tool is never
# a dependency to doctor, never reported as one no import line names, and
# needs no hash
# EZ-LED-5
law doctor_ignores_tools:
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +cs: List<&2, DP.Note>
  for +t1: String
  for +t2: String
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for ts1: List<&2, M.Tool>
  for ts2: List<&2, M.Tool>
  for g1: {M.Good{M.Manifest{n, e, b, hub, ds, ts1}} == M.parse(t1) : M.Read}
  for g2: {M.Good{M.Manifest{n, e, b, hub, ds, ts2}} == M.parse(t2) : M.Read}
  {DP.plan.of(DP.ledger.seen(M.parse(t1)), cc, lib, lock, rs, cs)
    == DP.plan.of(DP.ledger.seen(M.parse(t2)), cc, lib, lock, rs, cs) : P.Plan}

# LAW: with no ez.toml, `ez doctor` fails, after saying what else it found
law doctor_needs_ledger:
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  {DP.refuses(DW.World{cc, lib, None{}, lock, rs}) == True{} : Bool}

# LAW: and with one that does not parse
law doctor_refuses_unread:
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +s: String
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {DP.refuses(DW.World{cc, lib, Some{s}, lock, rs}) == True{} : Bool}

# LAW: a ledger with no dependencies never makes the lock a problem, whatever
# the lock names, so `ez doctor` passes a project that has nothing to lock
law lock_needless:
  for hs: List<&2, String>
  {DP.lock.wrong(0n, hs) == False{} : Bool}

# LAW: a ledger with dependencies and a lock that names no package is one
law lock_needed:
  for n: Nat
  {DP.lock.wrong(1n+n, []) == True{} : Bool}

# LAW: a lock that names a package is never one, however many the ledger has
law lock_names:
  for deps: Nat
  for h: String
  for t: List<&2, String>
  {DP.lock.wrong(deps, h <> t) == False{} : Bool}

# LAW: a lock the lock planner would write as it stands is not reported stale:
# when a lock is there, the sources were listed, the lock planner has every
# answer it asks for on the World doctor gathered, about packages and about
# names, and the lock it decides on
# is the lock's text byte for byte, the check's one line is that the lock is
# up to date, and it is not a problem
# EZ-VEN-6
law doctor_passes_fresh_lock:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{t} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  {DP.checked(w) == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}

# LAW: and doctor says so
# EZ-VEN-6
law doctor_says_fresh_lock:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{t} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  {DP.said(DP.plan(w), DP.fresh.line()) == True{} : Bool}

# LAW: a lock that differs by any byte from the lock the lock planner decides
# on is reported stale, with the one line that says so
# EZ-VEN-6
law doctor_reports_stale_lock:
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
  {DP.said(DP.plan(w), DP.stale.line()) == True{} : Bool}

# LAW: and a stale lock fails `ez doctor`, so it exits 1
# EZ-VEN-6
law doctor_stale_lock_fails:
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
  {DP.refuses(w) == True{} : Bool}

# LAW: a lock doctor cannot judge offline, because the lock planner still
# asks about a package BEND_LIB did not hold, fails `ez doctor` too, rather
# than being passed on a guess
# EZ-VEN-6
law doctor_unchecked_lock_fails:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {a <> as == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.refuses(w) == True{} : Bool}

# LAW: and so does one it cannot judge because the lock planner still asks
# what a name names, whose file BEND_LIB does not hold: doctor never asks the
# hub, so it never judges a name by the network
# EZ-VEN-6
law doctor_unchecked_names_fail:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {a <> as == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.refuses(w) == True{} : Bool}

# LAW: a name the lock records whose file under BEND_LIB is missing, or names
# another hash than the lock does, fails `ez doctor`: bend reads that file
# before it would ask the hub, so a wrong one builds another package
# EZ-HUB-4
law doctor_wrong_name_fails:
  for +w: DW.World
  for x: String
  for xs: List<&2, String>
  for b: {x <> xs == DP.names.wrong(DP.lock.names(DW.lock(w)), DW.replies(w)) : List<&2, String>}
  {DP.refuses(w) == True{} : Bool}
