# `ez doctor` reports every hash an import line names that the ledger does
# not, and every ledger dependency no import line names, and exits 1 when it
# reports any.
#
# laws/DoctorWritesNothing.bend and laws/DoctorReportsDrift.bend are proved
# over the plan `ez doctor` runs (`src/doctor/plan.bend`). Its plan is lines
# said and how the command ends, so it writes, lays and removes nothing
# (`doctor_writes_nothing`). An import line names a hash when `ez lock`
# reads it so: the header imports of a `.bend` file git tracks outside
# `.ez/`, as the package walk scans them (`P.roots`). Over a ledger that
# reads, every such hash the ledger's dependencies lack has its line
# (`doctor_reports_unrecorded`), every dependency whose hash no such line
# names has its line (`doctor_reports_unused`), and a report with any line
# fails the command (`doctor_drift_fails`). A ledger that is not there or
# does not read fails the command before any comparison. That the
# interpreter hands doctor the tracked files as git lists them and their
# texts as they are on disk is trusted in src/ez/app.bend.
#
# An import line names a hash when the lock reads it so: `P.roots(fs)` is
# every hub package the header of a tracked `.bend` file outside `.ez/`
# imports, as the package walk scans it, and it is what `ez lock` resolves.
# `DW.sources(w)` is the answer the World holds for the sources, which the
# interpreter asks for whenever the ledger reads.
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W

# LAW: every hash an import line names that the ledger's dependencies do not
# is reported, on its own line
law doctor_reports_unrecorded:
  for +w: DW.World
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  for +fs: List<&2, W.Source>
  for +h: String
  for g: {M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, ts}} == DW.read(w) : M.Read}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for i: {DP.has(P.roots(fs), h) == True{} : Bool}
  for u: {False{} == DP.has(DP.pinned(ds), h) : Bool}
  {DP.said(DP.plan(w), DP.unrecorded.line(h)) == True{} : Bool}

# LAW: and every dependency of the ledger that no import line names, by its
# hash or by the name the ledger records it by, is reported, on its own line,
# wherever it stands in the ledger
law doctor_reports_unused:
  for +w: DW.World
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +pre: List<&2, M.Dep>
  for +d: M.Dep
  for +post: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  for +fs: List<&2, W.Source>
  for g: {M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, List.append(&2, M.Dep, pre, d <> post), ts}}
    == DW.read(w) : M.Read}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for u: {False{} == DP.used(DP.imports(fs), d) : Bool}
  {DP.said(DP.plan(w), DP.unused.line(d)) == True{} : Bool}

# LAW: and when the report holds any line, `ez doctor` fails, so it exits 1
law doctor_drift_fails:
  for +w: DW.World
  for +n: String
  for +e: String
  for +b: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  for +fs: List<&2, W.Source>
  for +x: String
  for +xs: List<&2, String>
  for g: {M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, ts}} == DW.read(w) : M.Read}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for r: {DP.drift.of(fs, ds) == x <> xs : List<&2, String>}
  {DP.refuses(w) == True{} : Bool}
