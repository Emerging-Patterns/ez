# proofs of laws/ToolSectionIsNoDependency.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/lock.bend as L
import ../src/doctor/plan.bend as DP
import ../laws/AddDependencyIdempotent.bend as L1
import ../laws/RemoveDependencyIdempotent.bend as L2
import ../laws/RemoveRefusesAbsent.bend as L3
import ../laws/ToolSectionIsNoDependency.bend as Laws
import ./lemmas/AbsentNameRefused.bend as M1
import ./lemmas/AddPlanEffects.bend as M2
import ./lemmas/PlanEffectFacts.bend as M3

# ---------------------------------------------------------------------------
# laws/ToolSectionIsNoDependency.bend: a `[tools.*]` section is judged at
# its own head, where its name does not start `deps.`, and every section
# before it is passed over the same way on both sides, so each law is an
# induction over the sections before it.

def Laws.tool_section_not_dep(ss1, n, ps, ss2):
  match ss1:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>,
        x => M.deps.put(String.starts_with(M.name_of(h), "deps."), h, x),
        M.deps(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2)),
        M.deps(List.append(&2, T.Sect, t, ss2)),
        Laws.tool_section_not_dep(t, n, ps, ss2))

# LAW: a section filed ahead of two lists of tools is filed ahead of the first
law tools_put_append:
  for b: Bool
  for +h: T.Sect
  for xs: List<&2, M.Tool>
  for +ys: List<&2, M.Tool>
  {M.tools.put(b, h, List.append(&2, M.Tool, xs, ys))
    == List.append(&2, M.Tool, M.tools.put(b, h, xs), ys) : List<&2, M.Tool>}

def tools_put_append(b, h, _xs, _ys):
  match b:
    case True{}:
      match h:
        case T.Sect{_n, _ps}:
          {==}
    case False{}:
      {==}

def Laws.tool_section_is_tool(ss1, n, ps, ss2):
  match ss1:
    case []:
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.tools.put(_, T.Sect{"tools." ++ n, ps}, M.tools(ss2))
          == M.tool_of("tools." ++ n, ps) <> M.tools(ss2) : List<&2, M.Tool>}
      {==}
    case +h <> +t:
      Equal.trans(List<&2, M.Tool>,
        M.tools.put(String.starts_with(M.name_of(h), "tools."), h,
          M.tools(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2))),
        M.tools.put(String.starts_with(M.name_of(h), "tools."), h,
          List.append(&2, M.Tool, M.tools(t), M.tool_of("tools." ++ n, ps) <> M.tools(ss2))),
        List.append(&2, M.Tool,
          M.tools.put(String.starts_with(M.name_of(h), "tools."), h, M.tools(t)),
          M.tool_of("tools." ++ n, ps) <> M.tools(ss2)),
        Equal.cong(List<&2, M.Tool>, List<&2, M.Tool>,
          x => M.tools.put(String.starts_with(M.name_of(h), "tools."), h, x),
          M.tools(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2)),
          List.append(&2, M.Tool, M.tools(t), M.tool_of("tools." ++ n, ps) <> M.tools(ss2)),
          Laws.tool_section_is_tool(t, n, ps, ss2)),
        tools_put_append(String.starts_with(M.name_of(h), "tools."), h, M.tools(t),
          M.tool_of("tools." ++ n, ps) <> M.tools(ss2)))

def Laws.tool_needs_no_hash(ss1, n, ps, ss2):
  match ss1:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(String, String,
        x => M.missing.at(M.missing.is(h), M.name_of(h), x),
        M.missing(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2)),
        M.missing(List.append(&2, T.Sect, t, ss2)),
        Laws.tool_needs_no_hash(t, n, ps, ss2))

# ---------------------------------------------------------------------------
# laws/ToolSectionIsNoDependency.bend

# Both ledgers are seen without their tools, which is the same ledger.
def Laws.doctor_ignores_tools(cc, lib, lock, rs, cs, _t1, t2, n, e, b, hub, hubpa, hubpv, ds, ts1, _ts2, g1, g2):
  %g1 : {DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs, cs)
    == DP.plan.of(DP.ledger.seen(M.parse(t2)), cc, lib, lock, rs, cs) : P.Plan}
  %g2 : {DP.plan.of(DP.ledger.seen(M.Good{M.Manifest{n, e, b, hub, hubpa, hubpv, ds, ts1}}), cc, lib, lock,
    rs, cs) == DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs, cs) : P.Plan}
  {==}

# laws/ToolSectionIsNoDependency.bend: the origins are read off the parsed
# ledger's dependencies, so the ledger is rewritten into the model the
# premise names and the tools are never looked at.
def Laws.lock_origins_skip_tools(_s, _n, _e, _b, _h, _hpa, _hpv, ds, _ts, g):
  %g : {L.ledger.read(_) == L.ledger.origins(ds) : List<&2, L.Origin>}
  {==}

def Laws.upgrade_origins_skip_tools(_nx, _n, _e, _b, _h, _hpa, _hpv, ds, _ts, g):
  %g : {L.ledger.read(_) == L.ledger.origins(ds) : List<&2, L.Origin>}
  {==}

# laws/ToolSectionIsNoDependency.bend: `Rend.add.keep` edits the
# dependencies and hands the tools on as they are, so the ledger
# `add_edits_ledger` names is this one.
def Laws.add_keeps_tools(w, n, e, b, h, hpa, hpv, ds, ts, good, ok):
  L1.add_edits_ledger(w, M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, good, ok)

# laws/ToolSectionIsNoDependency.bend: `Rend.remove` edits the dependencies
# and hands the tools on as they are, and a name that only a tool has is a
# name the dependencies lack, which `remove_refuses_absent` refuses whatever
# the tools are.
def Laws.remove_keeps_tools(name, s, ignore, n, e, b, h, hpa, hpv, ds, ts, good, ok):
  L2.remove_edits_ledger(name, s, ignore, M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, good, ok)

def Laws.remove_refuses_tool(name, s, ignore, n, e, b, h, hpa, hpv, ds, ts, good, _tool, no):
  L3.remove_refuses_absent(name, s, ignore, M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, good, no)
