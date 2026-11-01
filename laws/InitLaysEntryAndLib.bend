# With nothing at the entry, the entry at the project's top and nothing at
# `src/lib.bend`, `ez init` writes `src/lib.bend` and an entry that imports
# it; an entry in a directory of its own is written alone. It never writes
# over an entry or a `src/lib.bend` that is already there.
import Base
import ../src/lock/plan.bend as P
import ../src/init/plan.bend as IP

# LAW: a new project with nothing at `main.bend` or `src/lib.bend` gets both:
# the library, and the stub that imports it
law init_lays_src:
  for +n: String
  for +d: String
  for +ig: Maybe<&2, String>
  for fit: {IP.fits(IP.name.or(n), "main.bend", d) == True{} : Bool}
  {P.put.plan(IP.plan(IP.World{n, "", d, None{}, ig, None{}, None{}}), "src/lib.bend") == P.Put{IP.lib()} : P.Wrote}

# LAW: and the stub it writes at `main.bend` is the one that imports it
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
