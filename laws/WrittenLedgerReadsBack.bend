# Every ledger ez writes is one `Rend.renderable` accepts, and so reads back
# to the model it was rendered from wherever eztoml's round trip holds
# (trusted in src/toml/toml.bend).
#
# This guarantee is proved relative to eztoml's round trip (trusted in
# src/toml/toml.bend). laws/defs/LedgerReadsBackPremise.bend states the
# read-back as a premise, `ReadsBack`: every ledger `Rend.renderable`
# accepts reads back, from the text `Rend.show` writes, as itself.
# `Rend.show` is eztoml's `render` of the document ez assembles
# (`Rend.text`) and `M.parse` reads through eztoml's `parse`, so the premise
# is eztoml's round trip, proved in eztoml v0.9.0, and ez's gate does not
# re-check it. What ez proves is the rest: every command that writes ez.toml
# refuses a ledger that is not renderable, with no effect
# (laws/RefusalWritesNothing.bend), and writes one that reads back, given
# the premise, as the model its laws are stated over: `ez init` the package
# and entry it was given (`init_ledger_reads_back`), `ez add` the ledger
# with the dependency added (`add_ledger_reads_back`,
# `add_named_reads_back`), and `ez remove` the ledger with it dropped
# (`remove_ledger_reads_back`). `renderable` refuses a name or value holding
# `"`, `\` or a newline, a dependency with no hash, and a git source that
# names no repo or no root. A ledger written before ez used eztoml 0.4 reads
# to the same model: `src/toml/toml.bend` passes over the tables a dotted
# header implies, and `tests/toml.bend` reads an old ledger and lock and
# their new forms to the same sections.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/init/plan.bend as IP
import ../src/remove/plan.bend as RP
import ./defs/LedgerReadsBackPremise.bend as D1

# LAW: and the ledger it writes there reads back as that ledger. A ledger
# that could not be written so that it reads back is refused, with no effect.
law add_ledger_reads_back:
  for +w: A.World
  for +m: M.Manifest
  for +good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  for +text: String
  for put: {P.put.plan(AP.plan(w), "ez.toml") == P.Put{text} : P.Wrote}
  for rb: D1.ReadsBack()
  {M.parse(text) == M.Good{Rend.add.keep(m, AP.added(w))} : M.Read}

# LAW: a ledger that could not be written so that it reads back is refused
law add_named_refuses_unrenderable:
  for +w: A.World
  for bad: {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), H.added(w)))
    == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: and that ledger reads back as itself
law add_named_reads_back:
  for +w: A.World
  for +m: M.Manifest
  for +good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {H.refuses(w) == False{} : Bool}
  for +text: String
  for put: {P.put.plan(H.plan(w), "ez.toml") == P.Put{text} : P.Wrote}
  for rb: D1.ReadsBack()
  {M.parse(text) == M.Good{Rend.add.keep(m, H.added(w))} : M.Read}

# LAW: the ledger `ez init` writes reads back as the one it made: the package
# and entry asked for, or `app` and `main.bend`, and nothing else. A name or
# entry the ledger cannot carry is refused, with no effect, rather than
# written as a file that reads back as something else.
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
  for rb: D1.ReadsBack()
  {M.parse(text) == M.Good{IP.model(IP.name.or(n), IP.entry.or(e))} : M.Read}

# LAW: and the ledger it writes there reads back as the ledger `Rend.remove`
# gave. A ledger that, with the dependency dropped, could not be written so
# that it reads back is refused, with no effect.
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
  for rb: D1.ReadsBack()
  {M.parse(text) == M.Good{Rend.remove(m, name)} : M.Read}
