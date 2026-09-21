# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L
import ../manifest/toml.bend as T
import ../pkg/pkg.bend as K

# LAW: a package resolves to the origin recorded for it, whatever origins
# follow. A second record of the same hash never shadows the first, so each of
# ez.toml and `.ez/origins.toml` is read the way it was written.
law origin_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.origin(L.Origin{h, s} <> rest, h) == s : L.Src}

# LAW: a package resolves to the same origin whether the ledger recorded it or
# the cache did. This is the property the tool exists for: a fresh clone has
# ez.toml and no `.ez/origins.toml` at all, and it must lock what a working
# checkout locks. It also says the ledger wins outright, since the cache it is
# quantified over is any cache, including one recording the same hash
# differently.
law origin_agrees:
  for +h: String
  for +s: L.Src
  for cache: List<&2, L.Origin>
  {L.origin(L.origins.all([L.Origin{h, s}], cache), h)
    == L.origin(L.origins.all([], [L.Origin{h, s}]), h) : L.Src}

# The shape lock/lock.bend's "have I read this file" scan had before this pass
# rewrote it for cost, kept here so the rewrite's risk can be stated rather
# than sampled, the way net/LAWS.bend keeps the shapes net/http.bend had
# before its dechunk rewrite. Nothing but the law below reads it.
#
# `Bool.or` is an ordinary function and reduces both of its sides, so a scan
# written with it reads the whole list even when the head answers. This list
# grows by one with every file the project walk reads, which makes the scan
# the inner half of a quadratic.
def old.seen.holds(xs: List<&2, String>, +s: String) -> Bool:
  match xs:
    case []:
      False{}
    case +h <> t:
      Bool.or(String.eq(h, s), old.seen.holds(t, s))

# LAW: the scan that stops at the name it was looking for answers what the
# scan that read past it answered, on every list and every name.
law seen_holds_agrees:
  for xs: List<&2, String>
  for +s: String
  {old.seen.holds(xs, s) == L.seen.holds(xs, s) : Bool}

# The rest of the lock document: the order packages are written in, the
# `0x` name an import carries, and that a lock that was written reads
# back as the lock it was. A lock that names packages in walk order
# instead of hash order is a different file on every machine, and an
# import that kept the path as part of the hash is a package the hub
# has never seen.

# whether a string holds no `/`, and so is one component of a spec
def slashless(s: String) -> Bool:
  match s:
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
# it holds and whatever bend wrote it.
law lock_names_hub:
  for +hub: String
  for ver: String
  for ps: List<&2, L.Pack>
  {L.lock.hub(L.doc(hub, ver, ps)) == hub : String}

# a hub package and a vendored one, the two shapes a lock records
def sample.packs() -> List<&2, L.Pack>:
  [L.Pack{"0xbb", L.Hub{}, [K.File{"src/lib.bend", "ab"}]},
   L.Pack{"0xaa", L.Git{"https://h/r", "c0ffee", "src/lib.bend", ".",
     "sha256-zz", "v1.0"}, [K.File{"lib.bend", "cd"}]}]

# LAW: packages are written in hash order. The walk found `0xbb` first;
# the document names `0xaa` first.
law hashes_sorted:
  {L.hashes(L.doc("https://hub.bend-lang.com", "2.0.16", sample.packs()))
    == ["0xaa", "0xbb"] : List<&2, String>}

# LAW: what was written reads back as what it was. The lock as text is
# the lock as a document, so a file `ez lock` wrote is the file the
# next lock reads.
law lock_roundtrip:
  {L.packs(T.sects(T.parse(L.render("https://hub.bend-lang.com",
    "2.0.16", sample.packs()))))
    == L.pack.sort(sample.packs()) : List<&2, L.Pack>}
