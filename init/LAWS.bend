# init: the laws. The human states them; PROOF.bend must prove them. They
# are stated over the plan `ez init` runs (init/plan.bend), so what they say
# of the plan is what the command does, the interpreter's faithfulness being
# EZ-TRUST-2.
import Base
import ./plan.bend as IP
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/LAWS.bend as ML
import ../pub/blurb.bend as B

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
  for desc: String
  for s: String
  for ignore: Maybe<&2, String>
  for main: Maybe<&2, String>
  for lib: Maybe<&2, String>
  {P.writes(IP.plan(IP.World{name, entry, desc, Some{s}, ignore, main, lib})) == False{} : Bool}

# LAW: the ledger `ez init` writes reads back as the one it made: the package
# and entry asked for, or `app` and `main.bend`, and nothing else. A name or
# entry the ledger cannot carry is refused, with no effect, rather than
# written as a file that reads back as something else.
# EZ-LED-4
law init_ledger_reads_back:
  for +n: String
  for +e: String
  for +d: String
  for led: Maybe<&2, String>
  for ig: Maybe<&2, String>
  for mn: Maybe<&2, String>
  for lb: Maybe<&2, String>
  for +text: String
  for put: {P.put.plan(IP.plan(IP.World{n, e, d, led, ig, mn, lb}), "ez.toml") == P.Put{text} : P.Wrote}
  for rb: ML.ReadsBack()
  {M.parse(text) == M.Good{IP.model(IP.name.or(n), IP.entry.or(e))} : M.Read}

# LAW: the ledger `ez init` makes names no `publish-as` and no `version`,
# whatever the package and entry: with `init_ledger_reads_back` it reads back
# with both empty, so the project publishes by hash (`neither_is_hash`) until
# its author names both
# EZ-PUB-3
law init_publishes_by_hash:
  for +n: String
  for +e: String
  {IP.model(n, e) == M.Manifest{n, e, "", "", "", "", [], []} : M.Manifest}

# LAW: the stub `ez init` writes opens with its line for the hub, so that line
# is what the hub describes the package by (`B.blurb` reads a file's first
# line), whether or not the stub was laid out with a library
# EZ-INIT-1
law init_stub_heads:
  for +n: String
  for +d: String
  for +lays: Bool
  for one: {B.has.nl(IP.header(n, d)) == False{} : Bool}
  {B.line.first(IP.stub(n, d, lays)) == IP.header(n, d) : String}

# LAW: that line is `# <name>: <description>` for the description asked for
# EZ-INIT-1
law init_header_given:
  for +n: String
  for +d: String
  for some: {String.is_empty(d) == False{} : Bool}
  {IP.header(n, d) == "# " ++ n ++ ": " ++ d : String}

# LAW: and `# <name>: TODO describe <name>` when none was
# EZ-INIT-1
law init_header_placeholder:
  for +n: String
  {IP.header(n, "") == "# " ++ n ++ ": " ++ ("TODO describe " ++ n) : String}

# LAW: a description that would spill past the entry's first line, holding a
# newline, is refused, and so writes nothing (`init_refusal_writes_nothing`)
# EZ-INIT-1
law init_one_line:
  for +n: String
  for +e: String
  for +d: String
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +lb: Maybe<&2, String>
  for two: {B.has.nl(IP.header(IP.name.or(n), d)) == True{} : Bool}
  {IP.refuses(IP.World{n, e, d, None{}, ig, mn, lb}) == True{} : Bool}

# LAW: a new project with nothing at `main.bend` or `src/lib.bend` gets both:
# the library, and the stub that imports it
# EZ-INIT-2
law init_lays_src:
  for +n: String
  for +d: String
  for +ig: Maybe<&2, String>
  for fit: {IP.fits(IP.name.or(n), "main.bend", d) == True{} : Bool}
  {P.put.plan(IP.plan(IP.World{n, "", d, None{}, ig, None{}, None{}}), "src/lib.bend") == P.Put{IP.lib()} : P.Wrote}

# LAW: and the stub it writes at `main.bend` is the one that imports it
# EZ-INIT-2
law init_lays_main:
  for +n: String
  for +d: String
  for +ig: Maybe<&2, String>
  for fit: {IP.fits(IP.name.or(n), "main.bend", d) == True{} : Bool}
  {P.put.plan(IP.plan(IP.World{n, "", d, None{}, ig, None{}, None{}}), "main.bend")
    == P.Put{IP.stub(IP.name.or(n), d, True{})} : P.Wrote}

# LAW: a `src/lib.bend` that is already there is never written over, whatever
# else `ez init` finds, unless it is the entry asked for, which the entry's
# own text decides
# EZ-INIT-2
law init_keeps_src:
  for +n: String
  for +e: String
  for +d: String
  for +led: Maybe<&2, String>
  for +ig: Maybe<&2, String>
  for +mn: Maybe<&2, String>
  for +s: String
  for ne: {String.eq(IP.entry.or(e), "src/lib.bend") == False{} : Bool}
  {P.put.plan(IP.plan(IP.World{n, e, d, led, ig, mn, Some{s}}), "src/lib.bend") == P.Kept{} : P.Wrote}

# LAW: an entry that is already there is never written over, whatever else
# `ez init` finds, unless it is ez.toml or `.gitignore`, which ez writes
# itself
# EZ-INIT-2
law init_keeps_entry:
  for +n: String
  for +e: String
  for +d: String
  for +led: Maybe<&2, String>
  for +ig: Maybe<&2, String>
  for +s: String
  for +lb: Maybe<&2, String>
  for nt: {String.eq("ez.toml", IP.entry.or(e)) == False{} : Bool}
  for ng: {String.eq(".gitignore", IP.entry.or(e)) == False{} : Bool}
  {P.put.plan(IP.plan(IP.World{n, e, d, led, ig, Some{s}, lb}), IP.entry.or(e)) == P.Kept{} : P.Wrote}
