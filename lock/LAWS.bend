# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L

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
