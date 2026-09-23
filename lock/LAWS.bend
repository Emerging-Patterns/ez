# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L
import ./world.bend as W
import ./plan.bend as P
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T

# LAW: a package resolves to the origin recorded for it, whatever origins
# follow. A second record of the same hash never shadows the first, so the
# ledger is read the way it was written.
law origin_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.origin(L.Origin{h, s} <> rest, h) == s : L.Src}

# LAW: a package the ledger records is named, whatever it records after it.
# Only a package no record names is fetched from the hub on nothing but its
# hash, and so only such a package can stop a lock for being unnamed.
law known_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.known(L.Origin{h, s} <> rest, h) == True{} : Bool}

# LAW: a fetched checkout whose NAR hash is the one the ledger records passes,
# and the lock goes on to lay it out.
law nar_why_agrees:
  for +n: String
  for url: String
  for rev: String
  for f: {False{} == String.is_empty(n) : Bool}
  {L.nar.why(n, n, url, rev) == "" : String}

# LAW: one whose NAR hash is any other is refused. The reason is never empty,
# and an empty reason is the only one `fetch.judge` lets through.
law nar_why_refuses:
  for +want: String
  for +got: String
  for url: String
  for rev: String
  for f: {False{} == String.is_empty(want) : Bool}
  for d: {False{} == String.eq(want, got) : Bool}
  {String.is_empty(L.nar.why(want, got, url, rev)) == False{} : Bool}

# LAW: and a ledger that records no NAR hash has nothing to check a checkout
# against, so the checkout is refused whatever it hashes to
law nar_why_needs_a_hash:
  for got: String
  for url: String
  for rev: String
  {String.is_empty(L.nar.why("", got, url, rev)) == False{} : Bool}

# The rest of the lock document: the order packages are written in, the
# `0x` name an import carries, and that a lock that was written reads
# back as the lock it was. A lock that names packages in walk order
# instead of hash order is a different file on every machine, and an
# import that kept the path as part of the hash is a package the hub
# has never seen.

# whether a string holds no `/`, and so is one component of a spec
def slashless(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(Char.is_eq(h, '/')), slashless(t))

# LAW: an import names the package before its first slash. The hash is
# the first component, and everything after the slash is the path
# inside the package.
law spec_hash:
  for +h: String
  for +rest: String
  for +e: {slashless(h) == True{} : Bool}
  {L.spec.hash(String.append(h, SCon{'/', rest})) == h : String}

# LAW: a package that sorts at or before the head of a list already in
# order is written first. Insertion is what puts packages in hash
# order, so a lock is the same text however the walk found them.
law pack_ins_le:
  for +x: L.Pack
  for +h: L.Pack
  for t: List<&2, L.Pack>
  for e: {True{} == L.pack.le(x, h) : Bool}
  {L.pack.ins(h <> t, x) == x <> (h <> t) : List<&2, L.Pack>}

# LAW: a lock names the hub it was resolved against, whatever packages
# it holds.
law lock_names_hub:
  for +hub: String
  for ps: List<&2, L.Pack>
  {L.lock.hub(L.doc(hub, ps)) == hub : String}

# LAW: a lock with no tools is the lock `render` writes. Packages do not
# move because a tool list was empty.
law render_keeps_packages_without_tools:
  for +hub: String
  for ps: List<&2, L.Pack>
  {L.render.pick(True{}, hub, ps, []) == L.render(hub, ps) : String}

# The planner (plan.bend) over the World (world.bend). Every law below is
# about what plain `ez lock` does, stated over the plan it returns; the
# interpreter that executes the plan is EZ-TRUST-2.

# what a plan leaves at the lock's path, from what the planner decided. Law
# vocabulary: ez never calls it.
def put.doc(doc: P.Doc) -> P.Wrote:
  match doc:
    case P.Doc{text}:
      P.Put{text}
    case P.Stop{_why}:
      P.Kept{}

# LAW: the lock depends on nothing in a World but its Inputs: the ledger, the
# committed sources, and the verdict on every answer. Two Worlds that agree on
# those write the same bytes to ez.lock.toml, or both write none, however they
# differ otherwise.
# EZ-DOC-3
law lock_reproducible:
  for w1: W.World
  for w2: W.World
  for e: {W.inputs(w1) == W.inputs(w2) : W.Inputs}
  {P.put(w1, "ez.lock.toml") == P.put(w2, "ez.lock.toml") : P.Wrote}

# LAW: a working checkout, whose git trees are read from BEND_LIB, writes the
# lock a fresh clone writes, which has none there and clones and weighs each
# one at its pinned rev, so long as git hands the clone the same bytes.
# EZ-DOC-3
law clone_reproduces:
  for +w: W.World
  {P.put(W.reclone(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# LAW: a plain lock never writes ez.toml
# EZ-DOC-5
law plain_lock_keeps_ledger:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.put(w, "ez.toml") == P.Kept{} : P.Wrote}

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

# LAW: every package a plain lock resolves, and so every package its lock
# renders, carries the source ez.toml records for its hash. Tools are
# rendered from the ledger's `[tools.*]` alone, as `M.tools_of` reads them.
# EZ-DOC-5
law plain_lock_pins_ledger_sources:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {pinned.all(W.origins(W.ledger.of(w)), P.packs(w)) == P.packs(w)
    : List<&2, L.Pack>}

# LAW: a plain lock that refuses writes, lays and removes nothing. Its plan
# has no effect at all; the reason is how it ends. This is EZ-OUT-2 for a
# plain lock, and it is tagged once `--upgrade` is planned too.
law lock_refusal_writes_nothing:
  for +w: W.World
  for r: {P.refuses(w) == True{} : Bool}
  {P.writes(P.plan(w)) == False{} : Bool}

# LAW: a tree read from BEND_LIB is judged exactly as the same bytes cloned
# at the pinned rev and weighed to the ledger's narHash
law lib_judged_as_clone:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept(orgs, hub, hash, W.Got{W.Lib{}, manifest, ss})
    == W.accept(orgs, hub, hash,
      W.Got{W.Clone{L.src.nar(L.origin(orgs, hash))}, manifest, ss})
    : W.Verdict}

# LAW: every package the walk resolves carries the source the ledger records
# for its hash, one step at a time
law walk_pins_ledger_sources:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {pinned.all(orgs, P.walk.packs(P.walk(fuel, orgs, js, wk)))
    == P.walk.packs(P.walk(fuel, orgs, js, wk)) : List<&2, L.Pack>}

# LAW: a tracked path under `.ez/` is never a root of the lock. The trees
# there are packages, read as packages, and not the project's own sources.
law root_skips_ez:
  for +p: String
  for text: String
  {P.roots.one(W.Source{".ez/" ++ p, text}) == [] : List<&2, String>}

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
