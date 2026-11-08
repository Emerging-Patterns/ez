# A `[tools.*]` section is a tool, never a dependency, and needs no `hash`.
#
# This guarantee is proved over the ledger reader and over every command
# that reads a ledger's dependencies. The reader files a `[tools.*]` section
# among the tools, never among the dependencies, and never refuses it for
# lacking a `hash`, wherever it stands (`tool_section_not_dep`,
# `tool_section_is_tool`, `tool_needs_no_hash`). `ez lock`, plain or
# `--upgrade`, reads packages by the origins of the dependencies alone
# (`lock_origins_skip_tools`, `upgrade_origins_skip_tools`); `ez add` and
# `ez remove` edit the dependencies and write the tools back as they read
# them (`add_keeps_tools`, `remove_keeps_tools`), and `ez remove` refuses a
# name only a tool has (`remove_refuses_tool`); and two ledgers that differ
# only in their tools make the same `ez doctor` plan around the same lock
# check (`doctor_ignores_tools`), the check alone reading them, since the
# lock records them. `ez fetch` reads no dependency of the ledger, and `ez
# tool` reads only its tools.
import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/remove/plan.bend as RP

# A `[tools.*]` section is a pinned CLI and nothing else: the reader files it
# among the tools, never among the dependencies, and never asks it for a
# `hash`, wherever it stands in the ledger. Every command reads the ledger
# through this reader, so what it says holds of each of them.

# LAW: a `[tools.*]` section adds no dependency
law tool_section_not_dep:
  for ss1: List<&2, T.Sect>
  for +n: String
  for +ps: List<&2, T.Kv>
  for +ss2: List<&2, T.Sect>
  {M.deps(List.append(&2, T.Sect, ss1, T.Sect{"tools." ++ n, ps} <> ss2))
    == M.deps(List.append(&2, T.Sect, ss1, ss2)) : List<&2, M.Dep>}

# LAW: it is read as the tool it names, where it stands among the tools
law tool_section_is_tool:
  for ss1: List<&2, T.Sect>
  for +n: String
  for +ps: List<&2, T.Kv>
  for +ss2: List<&2, T.Sect>
  {M.tools(List.append(&2, T.Sect, ss1, T.Sect{"tools." ++ n, ps} <> ss2))
    == List.append(&2, M.Cli, M.tools(ss1), M.tool_of("tools." ++ n, ps) <> M.tools(ss2))
    : List<&2, M.Cli>}

# LAW: and it is never the section a ledger is refused for lacking a `hash`
law tool_needs_no_hash:
  for ss1: List<&2, T.Sect>
  for +n: String
  for +ps: List<&2, T.Kv>
  for +ss2: List<&2, T.Sect>
  {M.missing(List.append(&2, T.Sect, ss1, T.Sect{"tools." ++ n, ps} <> ss2))
    == M.missing(List.append(&2, T.Sect, ss1, ss2)) : String}

# LAW: a ledger's `[tools.*]` pins change nothing doctor says or how it ends
# outside the lock check, which compares the lock with the one `ez lock`
# writes and so reads the pins the lock records: two ledgers that differ only
# in their tools make the same plan around the same check, so a tool is never
# a dependency to doctor, never reported as one no import line names, and
# needs no hash
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
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for ts1: List<&2, M.Cli>
  for ts2: List<&2, M.Cli>
  for g1: {M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, ts1}} == M.parse(t1) : M.Read}
  for g2: {M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, ts2}} == M.parse(t2) : M.Read}
  {DP.plan.of(DP.ledger.seen(M.parse(t1)), cc, lib, lock, rs, cs)
    == DP.plan.of(DP.ledger.seen(M.parse(t2)), cc, lib, lock, rs, cs) : P.Plan}

# LAW: the origins `ez lock` reads packages by are the dependencies of
# ez.toml alone: a `[tools.*]` pin is never an origin, whatever tools the
# ledger pins. `ez lock --upgrade` reads the ledger it leaves the same way
# (`W.next.origins`, through `L.ledger.read`).
law lock_origins_skip_tools:
  for +s: String
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  for g: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(s) : M.Read}
  {W.origins(Some{s}) == L.ledger.origins(ds) : List<&2, L.Origin>}

# LAW: and so are the origins `ez lock --upgrade` reads packages by, over the
# ledger the upgrade leaves, whatever tools that ledger pins
law upgrade_origins_skip_tools:
  for +nx: Up.Next
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  for g: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == Up.next.read(nx) : M.Read}
  {W.next.origins(nx) == L.ledger.origins(ds) : List<&2, L.Origin>}

# LAW: `ez add` records the dependency among the dependencies and keeps the
# ledger's `[tools.*]` pins as they were: the ledger it writes has the tools
# it read, and its dependencies are the ones it read with the one added
law add_keeps_tools:
  for +w: A.World
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for good: {A.read(w) == M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  {P.put.plan(AP.plan(w), "ez.toml")
    == P.Put{Rend.show(M.Manifest{n, e, b, h, hpa, hpv,
      List.append(&2, M.Dep, Rend.without(ds, M.dep.name(Rend.readd(ds, AP.added(w)))),
        [Rend.readd(ds, AP.added(w))]), ts})} : P.Wrote}

# LAW: `ez remove` drops a dependency and keeps the ledger's `[tools.*]`
# pins as they were: the ledger it writes has the tools it read
law remove_keeps_tools:
  for +name: String
  for +s: String
  for +ignore: String
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +good: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(s) : M.Read}
  for ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  {P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml")
    == P.Put{Rend.show(M.Manifest{n, e, b, h, hpa, hpv, Rend.without(ds, name), ts})} : P.Wrote}

# LAW: and a name the ledger pins only as a tool is no dependency to remove:
# `ez remove` refuses it and writes nothing, so the tool stays
law remove_refuses_tool:
  for +name: String
  for +s: String
  for +ignore: String
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for good: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(s) : M.Read}
  for tool: {M.tool.has(ts, name) == True{} : Bool}
  for no: {False{} == RP.named(ds, name) : Bool}
  {RP.refuses(RP.World{name, Some{s}, ignore}) == True{} : Bool}
