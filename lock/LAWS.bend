# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../pkg/pkg.bend as K
import ../manifest/manifest.bend as M

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

# a hub package and a vendored one, the two shapes a lock records
def sample.packs() -> List<&2, L.Pack>:
  [L.Pack{"0xbb", L.Hub{}, [K.File{"src/lib.bend", "ab"}]},
   L.Pack{"0xaa", L.Git{"https://h/r", "c0ffee", "src/lib.bend", ".",
     "sha256-zz", "v1.0"}, [K.File{"lib.bend", "cd"}]}]

# LAW: packages are written in hash order. The walk found `0xbb` first;
# the document names `0xaa` first.
# toward EZ-DOC-2
law hashes_sorted:
  {L.hashes(L.doc("https://hub.bend-lang.com", sample.packs()))
    == ["0xaa", "0xbb"] : List<&2, String>}

# LAW: what was written reads back as what it was. The lock as text is
# the lock as a document, so a file `ez lock` wrote is the file the
# next lock reads.
# toward EZ-DOC-1
law lock_roundtrip:
  {L.packs(T.sects(T.parse(L.render("https://hub.bend-lang.com",
    sample.packs()))))
    == L.pack.sort(sample.packs()) : List<&2, L.Pack>}

# a pinned CLI, the shape `[tools.*]` records
def sample.tool() -> M.Tool:
  M.Tool{"bolt", "bolt/main.bend", "",
    M.Git{"https://github.com/Emerging-Patterns/bolt",
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "v0.4.0", ".",
      "sha256-zz", False{}}}

# LAW: a lock with no tools is the lock `render` writes. Packages do not
# move because a tool list was empty.
law render_keeps_packages_without_tools:
  for +hub: String
  for ps: List<&2, L.Pack>
  {L.render.pick(True{}, hub, ps, []) == L.render(hub, ps) : String}

# LAW: a `[tools.*]` table is not a package. `restore` and `bendLib` read
# `packs`, and a tool pin does not join that list.
# toward EZ-LED-5
law tools_are_not_packages:
  {L.packs(T.sects(T.parse(L.render.pick(False{}, "https://hub.bend-lang.com",
    sample.packs(), [sample.tool()]))))
    == L.pack.sort(sample.packs()) : List<&2, L.Pack>}

# LAW: the commit written for a tool is the commit read back
# toward EZ-DOC-1
law tool_pin_reads_back:
  {M.source.rev(M.tool.source(M.tool.find(M.tools(T.sects(T.parse(
    L.render.pick(False{}, "https://hub.bend-lang.com", [],
      [sample.tool()])))), "bolt")))
    == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" : String}
