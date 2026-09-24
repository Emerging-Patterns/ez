# remove: the laws. The human states them; PROOF.bend must prove them. They
# are stated over the plan `ez remove` runs (remove/plan.bend), so what they
# say of the plan is what the command does, the interpreter's faithfulness
# being EZ-TRUST-2.
import Base
import ./plan.bend as RP
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/ignore.bend as I

# LAW: `ez remove` that refuses writes, lays and removes nothing: not
# ez.toml, not `.gitignore`, and no committed tree. Its plan has no effect at
# all; the reason is how it ends. No ledger, one that does not parse, and a
# name the ledger does not have are all such Worlds.
# EZ-OUT-2
law remove_refusal_writes_nothing:
  for +w: RP.World
  for r: {RP.refuses(w) == True{} : Bool}
  {P.writes(RP.plan(w)) == False{} : Bool}

# LAW: `ez remove` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
# EZ-OUT-1
law remove_exits_as_it_refuses:
  for +w: RP.World
  {P.code(RP.plan(w)) == P.status.of(RP.refuses(w)) : U32}

# LAW: with no ez.toml, `ez remove` refuses, whatever it was asked to remove
# and whatever `.gitignore` holds, so it writes nothing
# EZ-LED-6
law remove_needs_ledger:
  for +name: String
  for +ignore: String
  {RP.refuses(RP.World{name, None{}, ignore}) == True{} : Bool}

# LAW: a ledger that does not parse is refused, so `ez remove` writes no
# guess over it
# EZ-LED-1
law remove_refuses_unread:
  for +name: String
  for +s: String
  for +ignore: String
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {RP.refuses(RP.World{name, Some{s}, ignore}) == True{} : Bool}

# LAW: a name the ledger does not have is refused, as `cargo remove` refuses
# it, so removing it writes nothing
law remove_refuses_absent:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for good: {M.Good{m} == M.parse(s) : M.Read}
  for no: {False{} == RP.named(RP.deps.of(m), name) : Bool}
  {RP.refuses(RP.World{name, Some{s}, ignore}) == True{} : Bool}

# LAW: `ez remove` that does not refuse writes to ez.toml exactly the ledger
# `Rend.remove` gives, the edit `remove_idem` says is the same done twice
# EZ-LED-3
law remove_edits_ledger:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for +good: {M.Good{m} == M.parse(s) : M.Read}
  for ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  {P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml")
    == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}

# LAW: and leaves `.gitignore` holding exactly the file `I.sync` derives from
# the dependencies that are left: written when that changes it, kept as it
# was when it does not. `allowlist_is_the_ledger` and
# `allowlist_keeps_other_lines` say what that file's lines are.
# EZ-VEN-1
law remove_syncs_allowlist:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for +good: {M.Good{m} == M.parse(s) : M.Read}
  for ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  {RP.after(P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), ".gitignore"), ignore)
    == I.sync(RP.deps.of(Rend.remove(m, name)), ignore) : String}

# LAW: `ez remove` drops a dependency and keeps the ledger's `[tools.*]`
# pins as they were: the ledger it writes has the tools it read
# EZ-LED-5
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
  for +ts: List<&2, M.Tool>
  for +good: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(s) : M.Read}
  for ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  {P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml")
    == P.Put{Rend.show(M.Manifest{n, e, b, h, hpa, hpv, Rend.without(ds, name), ts})} : P.Wrote}

# LAW: and a name the ledger pins only as a tool is no dependency to remove:
# `ez remove` refuses it and writes nothing, so the tool stays
# EZ-LED-5
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
  for +ts: List<&2, M.Tool>
  for good: {M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} == M.parse(s) : M.Read}
  for tool: {M.tool.has(ts, name) == True{} : Bool}
  for no: {False{} == RP.named(ds, name) : Bool}
  {RP.refuses(RP.World{name, Some{s}, ignore}) == True{} : Bool}

# LAW: and the ledger it writes there reads back as the ledger `Rend.remove`
# gave. A ledger that, with the dependency dropped, could not be written so
# that it reads back is refused, with no effect.
# EZ-LED-4
law remove_ledger_reads_back:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for +text: String
  for +good: {M.Good{m} == M.parse(s) : M.Read}
  for +ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  for put: {P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml") == P.Put{text}
    : P.Wrote}
  {M.parse(text) == M.Good{Rend.remove(m, name)} : M.Read}
