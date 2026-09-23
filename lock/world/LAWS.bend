# lock/world: the laws of the planner spike. The human states them;
# PROOF.bend must prove them. None is tagged with a requirement: the planner
# they are about is not yet the one `ez lock` runs, so they prove nothing about
# ez lock itself. docs/rfc/ez-lock-planner.md says which requirement each
# becomes once it is.
import Base
import ./world.bend as W
import ../lock.bend as L
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T

# LAW: the lock depends on nothing in a World but its Inputs. Two Worlds that
# agree on the ledger, the committed sources, and the verdict on every reply
# lock the same way, however they differ otherwise.
law plan_frame:
  for w1: W.World
  for w2: W.World
  for e: {W.inputs(w1) == W.inputs(w2) : W.Inputs}
  {W.plan(w1) == W.plan(w2) : W.Outcome}

# LAW: a tree read from BEND_LIB is judged exactly as the same bytes cloned at
# the pinned rev and weighed to the ledger's narHash
law lib_judged_as_clone:
  for +orgs: List<&2, L.Origin>
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept(orgs, hash, W.Got{W.Lib{}, manifest, ss})
    == W.accept(orgs, hash,
      W.Got{W.Clone{L.src.nar(L.origin(orgs, hash))}, manifest, ss})
    : W.Verdict}

# LAW: a working checkout, whose git trees are read from BEND_LIB, locks
# exactly as a fresh clone does, which has none there and clones and weighs
# each one at its pinned rev, so long as git hands the clone the same bytes.
law clone_reproduces:
  for +ledger: String
  for listing: W.Listing
  for rs: List<&2, W.Reply>
  {W.plan(W.World{ledger, listing, W.reclone(W.origins(ledger), rs)})
    == W.plan(W.World{ledger, listing, rs}) : W.Outcome}

# A plain lock copies each package's source from the ledger and asks nothing
# about it. The walk is where that happens, one package at a time.

# a package with the source the ledger records for its hash. Law vocabulary:
# ez never calls it.
def pinned(+orgs: List<&2, L.Origin>, pack: L.Pack) -> L.Pack:
  L.Pack{+hash, _src, files} = pack
  L.Pack{hash, L.origin(orgs, hash), files}

# every package, so
def pinned.all(+orgs: List<&2, L.Origin>, ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match ps:
    case []:
      []
    case h <> t:
      pinned(orgs, h) <> pinned.all(orgs, t)

# the packages a walk has resolved
def packs.of(wk: W.Walk) -> List<&2, L.Pack>:
  W.Walk{_queue, packs, _asks, _bad} = wk
  packs

# LAW: every package the walk resolves carries the source the ledger records
# for its hash, so a plain lock pins every dependency where the ledger pins it
law walk_pins_ledger_sources:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +wk: W.Walk
  for +e: {pinned.all(orgs, packs.of(wk)) == packs.of(wk) : List<&2, L.Pack>}
  {pinned.all(orgs, packs.of(W.walk(fuel, orgs, js, wk)))
    == packs.of(W.walk(fuel, orgs, js, wk)) : List<&2, L.Pack>}

# The lock document. EZ-DOC-1 is a round trip through eztoml's reader, and
# the reader trims every line and strips the quotes off every value. These two
# laws are its first step: a quoted value survives both, whatever it holds.

# LAW: a quoted value is already trimmed. Its first and last characters are
# quotes, so no space it holds is at an end.
law trim_quoted:
  for +v: String
  {T.trim(T.quote(v)) == T.quote(v) : String}

# LAW: and stripping the quotes off gives the value back, even one that holds
# quotes of its own
law strip_quoted:
  for +v: String
  {T.strip(T.quote(v), '"', '"') == v : String}

# LAW: the reader cuts a pair line at every `=` and joins what follows the
# first one back with `=`. Joining a cut gives the text back, so a value that
# holds `=` of its own, as every narHash does, is read whole.
law join_split:
  for s: String
  for +c: Char
  {String.join(String.split(s, c), SCon{c, SNil{}}) == s : String}
