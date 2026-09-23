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

# LAW: and every dependency of the ledger that no import line names is
# reported, on its own line, wherever it stands in the ledger
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
  for u: {False{} == DP.has(P.roots(fs), M.dep.hash(d)) : Bool}
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

# LAW: a ledger's `[tools.*]` pins change nothing doctor asks, says or how it
# ends: two ledgers that differ only in their tools make the same step, so a
# tool is never a dependency to doctor, never reported as one no import line
# names, and needs no hash
# EZ-LED-5
law doctor_ignores_tools:
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
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
  {DP.step(DW.World{cc, lib, Some{t1}, lock, rs})
    == DP.step(DW.World{cc, lib, Some{t2}, lock, rs}) : DP.Step}

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
