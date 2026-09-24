# init: the laws. The human states them; PROOF.bend must prove them. They
# are stated over the plan `ez init` runs (init/plan.bend), so what they say
# of the plan is what the command does, the interpreter's faithfulness being
# EZ-TRUST-2.
import Base
import ./plan.bend as IP
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M

# LAW: `ez init` that refuses writes nothing: not ez.toml, not `.gitignore`,
# and no entry. Its plan has no effect at all; the reason is how it ends.
# EZ-OUT-2
law init_refusal_writes_nothing:
  for +w: IP.World
  for r: {IP.refuses(w) == True{} : Bool}
  {P.writes(IP.plan(w)) == False{} : Bool}

# LAW: `ez init` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
# EZ-OUT-1
law init_exits_as_it_refuses:
  for +w: IP.World
  {P.code(IP.plan(w)) == P.status.of(IP.refuses(w)) : U32}

# LAW: a ledger already on disk, whatever it holds, leaves `ez init` nothing
# to write, whatever it was asked for and whatever else is there, so the
# ledger's dependencies, tools and `bin` survive a second `ez init`
# EZ-LED-6
law init_keeps_ledger:
  for name: String
  for entry: String
  for s: String
  for ignore: Maybe<&2, String>
  for main: Maybe<&2, String>
  {P.writes(IP.plan(IP.World{name, entry, Some{s}, ignore, main})) == False{} : Bool}

# LAW: the ledger `ez init` writes reads back as the one it made: the package
# and entry asked for, or `app` and `main.bend`, and nothing else. A name or
# entry the ledger cannot carry is refused, with no effect, rather than
# written as a file that reads back as something else.
# EZ-LED-4
law init_ledger_reads_back:
  for +n: String
  for +e: String
  for led: Maybe<&2, String>
  for ig: Maybe<&2, String>
  for mn: Maybe<&2, String>
  for +text: String
  for put: {P.put.plan(IP.plan(IP.World{n, e, led, ig, mn}), "ez.toml") == P.Put{text} : P.Wrote}
  {M.parse(text) == M.Good{IP.model(IP.name.or(n), IP.entry.or(e))} : M.Read}
