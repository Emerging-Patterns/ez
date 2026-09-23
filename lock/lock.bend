# lock/lock: the lock document. What a package is (its source and its files),
# where the ledger says each package comes from, the imports a package's
# sources name, and the text of ez.lock.toml, written and read back. Nix reads
# the lock and fetches each file as a fixed-output derivation, so `bend` never
# touches the network inside the sandbox.
#
# A package resolves from the hub, or, when it was vendored from a repo that
# never published, from the git rev recorded for it. Both end up as the same
# BEND_LIB tree. ez.toml is the only record of where a package comes from.
#
# Everything here is pure. Deciding the lock is lock/plan.bend's, over the
# World lock/world.bend describes, and reading and writing are
# lock/run.bend's. `ez fetch` reads a lock back in fetch/plan.bend.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K

# where a package's bytes come from. A hub package needs nothing else; a git
# one pins a commit, the entry its hash was computed from, the directory inside
# the checkout its paths are written from, and the NAR hash nix rebuilds it by.
type Src is Data:
  Hub{}
  Git{url: String, rev: String, entry: String, root: String, nar: String, tag: String}

# a package the lock records
type Pack is Data:
  Pack{hash: String, src: Src, files: List<&2, K.File>}

# a package's origin, as ez.toml records it
type Origin is Data:
  Origin{hash: String, src: Src}

# the `0x` name an import carries, which is everything before its first `/`
def spec.hash(spec: String) -> String:
  K.word(String.split(spec, '/'), 0n)

# an import's package, or nothing when it names a module of this project
def spec.put(+spec: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, K.is_hub(spec), [spec.hash(spec)], [])

# every package a list of imports names
def specs(ms: List<&2, String>) -> List<&2, String>:
  match ms:
    case []:
      []
    case h <> t:
      List.append(&2, String, spec.put(h), specs(t))

# every package the sources of one package import
def kids(srcs: List<&2, String>) -> List<&2, String>:
  match srcs:
    case []:
      []
    case h <> t:
      List.append(&2, String, specs(K.scan.mods(K.scan(h))), kids(t))

# a table's path, as segments
def segs(sect: T.Sect) -> List<&2, String>:
  T.Sect{n, _ps} = sect
  T.segments(n)

# whether a table's path is these three segments
def is3(+ss: List<&2, String>, first: String, second: String, third: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 3n),
    Bool.and(String.eq(K.word(ss, 0n), first),
      Bool.and(String.eq(K.word(ss, 1n), second), String.eq(K.word(ss, 2n), third))))

# whether a table's path is one segment, this one
def named1(+ss: List<&2, String>, first: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 1n), String.eq(K.word(ss, 0n), first))

# whether a table's path is three segments, headed and tailed by these, whatever
# the hash between them is
def named3(+ss: List<&2, String>, first: String, third: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 3n),
    Bool.and(String.eq(K.word(ss, 0n), first), String.eq(K.word(ss, 2n), third)))

# the pairs of a table when it is the one asked for, otherwise the rest's
def at.pick(hit: Bool, sect: T.Sect, rest: List<&2, T.Kv>) -> List<&2, T.Kv>:
  match hit:
    case True{}:
      T.Sect{_n, ps} = sect
      ps
    case False{}:
      rest

# the pairs of the table at this three segment path, or none
def at3(ss: List<&2, T.Sect>, +first: String, +second: String, +third: String) -> List<&2, T.Kv>:
  match ss:
    case []:
      []
    case +h <> t:
      at.pick(is3(segs(h), first, second, third), h, at3(t, first, second, third))

# a git origin keeps every key it was written with; anything else is the hub
def src.go(git: Bool, +ps: List<&2, T.Kv>) -> Src:
  match git:
    case True{}:
      Git{T.value(ps, "url"), T.value(ps, "rev"), T.value(ps, "entry"),
        T.value(ps, "root"), T.value(ps, "narHash"), T.value(ps, "tag")}
    case False{}:
      Hub{}

# where a table says a package's bytes come from
def src_of(+ps: List<&2, T.Kv>) -> Src:
  src.go(String.eq(T.value(ps, "kind"), "git"), ps)

# a ledger's dependency as an origin: the repo and rev it names, or the hub.
# A hub dependency is recorded too, so that a package the ledger names is told
# apart from one it does not, which also resolves from the hub but is not
# vouched for by anything a clone has.
def ledger.put(git: Bool, +dep: M.Dep) -> List<&2, Origin>:
  match git:
    case True{}:
      [Origin{M.dep.hash(dep), Git{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), M.dep.entry(dep),
        M.source.root(M.source.dep(dep)), M.source.nar(M.source.dep(dep)),
        M.source.tag(M.source.dep(dep))}}]
    case False{}:
      [Origin{M.dep.hash(dep), Hub{}}]

# every origin a ledger's dependencies record, in the order written
def ledger.origins(ds: List<&2, M.Dep>) -> List<&2, Origin>:
  match ds:
    case []:
      []
    case +h <> t:
      List.append(&2, Origin,
        ledger.put(M.source.is_git(M.source.dep(h)), h), ledger.origins(t))

# every origin a ledger records. A ledger that would not parse records none,
# so a broken ez.toml leaves the lock exactly where it was without a guess.
def ledger.read(parsed: M.Read) -> List<&2, Origin>:
  match parsed:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, ds, _ts} = m
      ledger.origins(ds)

# this origin's source when the hash matches, otherwise whatever the rest gave
def origin.at(known: Origin, rest: Src, wanted: String) -> Src:
  Origin{n, s} = known
  Bool.pick(Src, String.eq(n, wanted), s, rest)

# where a package comes from, which is the hub unless an origin says otherwise
def origin(ds: List<&2, Origin>, +wanted: String) -> Src:
  match ds:
    case []:
      Hub{}
    case x <> t:
      origin.at(x, origin(t, wanted), wanted)

# the hash an origin is recorded under
def origin.hash(known: Origin) -> String:
  Origin{n, _s} = known
  n

# one `<sha256> <path>` line of a manifest
def line.put(+ws: List<&2, String>) -> List<&2, K.File>:
  Bool.pick(List<&2, K.File>, Nat.is_eq(List.length(&2, String, ws), 2n),
    [K.File{K.word(ws, 1n), K.word(ws, 0n)}], [])

# every file a manifest names
def manifest.files(ls: List<&2, String>) -> List<&2, K.File>:
  match ls:
    case []:
      []
    case h <> t:
      List.append(&2, K.File, line.put(K.words(h)), manifest.files(t))

# a url under the hub
def url_of(+hub: String, +hash: String, at: String) -> String:
  hub ++ "/" ++ hash ++ "/" ++ at

# bend accepts any prefix of the sha256, and a package's `0x` name is the first
# 32 characters of its manifest's digest
def want(+hash: String) -> String:
  String.drop(hash, 2n)

# why a fetched checkout is not the one the ledger pins, or "" when it is.
# The NAR hash is over the whole checkout, so a rev that no longer holds what
# it held when it was pinned is caught here, before anything is laid out. A
# ledger with no NAR hash has nothing to check the checkout against, and an
# unchecked tree is not one a lock may record.
def nar.why.go(none: Bool, same: Bool, +want: String, +got: String, +url: String, +rev: String) -> String:
  match none:
    case True{}:
      "ez: ez.toml records no narHash for " ++ url ++ " at " ++ rev ++
        ", so its tree cannot be checked; run `ez lock --upgrade` to pin it"
    case False{}:
      match same:
        case True{}:
          ""
        case False{}:
          "ez: " ++ url ++ " at " ++ rev ++ " has narHash " ++ got ++
            ", and ez.toml records " ++ want

def nar.why(+want: String, +got: String, +url: String, +rev: String) -> String:
  nar.why.go(String.is_empty(want), String.eq(want, got), want, got, url, rev)

# the hash a package is recorded under
def pack.hash(package: Pack) -> String:
  Pack{h, _s, _f} = package
  h

# one step of a scan that is looking for one hit. Every scan in this file
# wants it, so it is stated once here.
#
# `Bool.or` is an ordinary function and reduces both of its sides, so a scan
# written with it reads the whole list even when the head answers. The rest of
# the scan arrives as a thunk, which is a value, and only the arm that wants
# it applies it; handed in as an ordinary argument it would be reduced before
# this def could decline it.
def any.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether the ledger names a package. One it does not name still resolves from
# the hub, since the hub serves bytes by the hash they digest to, but when the
# hub does not have it there is nothing else to ask: nothing a clone has says
# where it came from, so the lock says that and stops.
def known(ds: List<&2, Origin>, +wanted: String) -> Bool:
  match ds:
    case []:
      False{}
    case x <> t:
      any.step(String.eq(origin.hash(x), wanted), _u => known(t, wanted))

# whether a package is already resolved. The wanted hash is compared first,
# the way pkg's `fresh` compares a path, so a walk that passes over a hash it
# has is a walk whose hashes are distinct without a symmetry lemma.
def has(ds: List<&2, Pack>, +wanted: String) -> Bool:
  match ds:
    case []:
      False{}
    case x <> t:
      any.step(String.eq(wanted, pack.hash(x)), _u => has(t, wanted))

# whether a name is already among the ones a walk has seen. Base's
# `List.contains` applies an erased equality, which Bend's termination check
# cannot see through; this scan is structural. `any.step` is what lets it
# stop at the name it was looking for instead of reading past it.
def seen.holds(xs: List<&2, String>, +needle: String) -> Bool:
  match xs:
    case []:
      False{}
    case +h <> t:
      any.step(String.eq(h, needle), _u => seen.holds(t, needle))

# a key worth writing, or nothing at all when its value is empty, so an absent
# tag leaves no trace
def kv(key: String, +val: String) -> List<&2, T.Kv>:
  Bool.pick(List<&2, T.Kv>, String.is_empty(val), [], [T.Kv{key, val}])

# the keys a source contributes to the lock
def src.pairs(source: Src) -> List<&2, T.Kv>:
  match source:
    case Hub{}:
      [T.Kv{"kind", "hub"}]
    case Git{url, rev, entry, root, nar, tag}:
      List.concat(&2, T.Kv,
        [[T.Kv{"kind", "git"}], kv("url", url), kv("rev", rev), kv("entry", entry),
         kv("root", root), kv("narHash", nar), kv("tag", tag)])

# a file of a package as a `"<path>" = "<sha256>"` pair
def file.pair(item: K.File) -> T.Kv:
  K.File{at, sum} = item
  T.Kv{at, sum}

# every file of a package, in path order
def file.pairs(fs: List<&2, K.File>) -> List<&2, T.Kv>:
  match fs:
    case []:
      []
    case h <> t:
      file.pair(h) <> file.pairs(t)

# the two tables a package is written as, from its files already in path
# order and each one once
def pack.sects.of(hash: String, src: Src, fs: List<&2, K.File>) -> List<&2, T.Sect>:
  +at = "packages." ++ T.quote(hash)
  [T.Sect{at ++ ".source", src.pairs(src)},
   T.Sect{at ++ ".files", file.pairs(fs)}]

# the two tables a package is written as
def pack.sects(package: Pack) -> List<&2, T.Sect>:
  Pack{hash, src, files} = package
  pack.sects.of(hash, src, K.files_of(files))

# every package, in hash order
def pack.all(ps: List<&2, Pack>) -> List<&2, T.Sect>:
  match ps:
    case []:
      []
    case h <> t:
      List.append(&2, T.Sect, pack.sects(h), pack.all(t))

# packages are written in hash order, so a lock is the same text however it was
# resolved
def pack.le(left: Pack, right: Pack) -> Bool:
  String.is_le(pack.hash(left), pack.hash(right))

# where a package goes among the packages already in order. The rest of the
# insertion is a parameter, because two defs that call each other are not
# allowed.
def pack.ins.put(le: Bool, item: Pack, head: Pack, tail: List<&2, Pack>, rest: List<&2, Pack>) -> List<&2, Pack>:
  match le:
    case True{}:
      item <> (head <> tail)
    case False{}:
      head <> rest

# a package inserted into a list already in hash order
def pack.ins(ps: List<&2, Pack>, +item: Pack) -> List<&2, Pack>:
  match ps:
    case []:
      [item]
    case Con{+h, +t}:
      pack.ins.put(pack.le(item, h), item, h, t, pack.ins(t, item))

# the packages in hash order. Insertion rather than Base's `List.sort`: that
# one is a fuelled bottom-up merge sort, whose recursion Bend cannot check, so
# it is reported as unsafe and every proof downstream of it inherits the
# report. An insertion sort shrinks its list at every step, so Bend checks it,
# and a lock names tens of packages, not thousands.
def pack.sort(ps: List<&2, Pack>) -> List<&2, Pack>:
  match ps:
    case []:
      []
    case Con{+h, t}:
      pack.ins(pack.sort(t), h)

# the `[lock]` table: what resolved the lock. The bend that ran the lock is
# not recorded: it is not something a clone has, and the flake pins the bend
# a build uses. A lock written before this that records one still reads,
# since nothing reads the key.
def lock.sect(hub: String) -> T.Sect:
  T.Sect{"lock", [T.Kv{"version", "2"}, T.Kv{"hub", hub}]}

# the lock as a document: what resolved it, then every package it resolved,
# in hash order. `render` writes its text a block at a time; that the two
# agree is lock/LAWS.bend's `render_is_doc`.
def doc(hub: String, ps: List<&2, Pack>) -> List<&2, T.Sect>:
  List.append(&2, T.Sect, [lock.sect(hub)], pack.all(pack.sort(ps)))

# a package's two tables as one block of text, filed under its hash. The lock
# puts packages in hash order by sorting these blocks with `K.file.sort`,
# whose order-independence pkg proves; a second sort over packages would need
# that proof again, and Bend's function values are linear, so one sort by a
# key function applied at every comparison cannot be written. A block's path
# is its package's hash, so distinct hashes are distinct paths.
def pack.block(package: Pack) -> K.File:
  Pack{+hash, src, files} = package
  K.File{hash, T.render(pack.sects.of(hash, src, K.files_of(files)))}

# every package, as its block
def pack.blocks(ps: List<&2, Pack>) -> List<&2, K.File>:
  match ps:
    case []:
      []
    case h <> t:
      pack.block(h) <> pack.blocks(t)

# the text of every block, in the order given
def block.texts(bs: List<&2, K.File>) -> List<&2, String>:
  match bs:
    case []:
      []
    case K.File{_hash, text} <> t:
      text <> block.texts(t)

# the lock's text: the `[lock]` table, each block in the order given, then the
# rest, one blank line between tables. A block is its two tables with the
# same blank line between them, so this is the text eztoml renders for the
# document.
def text.of(hub: String, bs: List<&2, K.File>, rest: List<&2, String>) -> String:
  String.join(T.render.sect(lock.sect(hub)) <>
    List.append(&2, String, block.texts(bs), rest), "\n")

# the lock as the text written to ez.lock.toml, its packages in hash order
def render(hub: String, ps: List<&2, Pack>) -> String:
  text.of(hub, K.file.sort(pack.blocks(ps)), [])

# the keys a pinned CLI contributes. The same names a `[tools.*]` section
# uses in ez.toml, and not the `[packages.*]` source table.
def tool.pairs(+entry: String, +binary: String, source: M.Source) -> List<&2, T.Kv>:
  match source:
    case M.Hub{}:
      List.concat(&2, T.Kv, [kv("entry", entry), kv("bin", binary)])
    case M.Git{url, rev, tag, root, nar, _vend}:
      List.concat(&2, T.Kv,
        [kv("git", url), kv("rev", rev), kv("tag", tag), kv("root", root),
         kv("narHash", nar), kv("entry", entry), kv("bin", binary)])

# one `[tools.<name>]` table
def tool.sect(pin: M.Tool) -> T.Sect:
  M.Tool{n, e, b, s} = pin
  T.Sect{"tools." ++ n, tool.pairs(e, b, s)}

# every pinned CLI, in the order the ledger holds them
def tool.sects(ts: List<&2, M.Tool>) -> List<&2, T.Sect>:
  match ts:
    case []:
      []
    case h <> t:
      tool.sect(h) <> tool.sects(t)

# the lock with its tools after the packages. An empty tool list adds no
# table, so a ledger with no tools writes the lock `render` writes.
def render.tools(ts: List<&2, M.Tool>, hub: String, ps: List<&2, Pack>) -> String:
  text.of(hub, K.file.sort(pack.blocks(ps)), T.render.all(tool.sects(ts)))

# the same, told whether the tool list is empty
def render.pick(empty: Bool, hub: String, ps: List<&2, Pack>, ts: List<&2, M.Tool>) -> String:
  match empty:
    case True{}:
      render(hub, ps)
    case False{}:
      render.tools(ts, hub, ps)

# the `[lock]` table of a lock that was read
def lock.pairs(ss: List<&2, T.Sect>) -> List<&2, T.Kv>:
  match ss:
    case []:
      []
    case +h <> t:
      at.pick(named1(segs(h), "lock"), h, lock.pairs(t))

# the hub a lock was resolved against
def lock.hub(ss: List<&2, T.Sect>) -> String:
  T.value(lock.pairs(ss), "hub")

# every hash a lock records, one per `[packages."<hash>".files]` table
def hash.put(hit: Bool, sect: T.Sect, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      T.Sect{n, _ps} = sect
      K.word(T.segments(n), 1n) <> rest
    case False{}:
      rest

# every hash a lock records
def hashes(ss: List<&2, T.Sect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case +h <> t:
      hash.put(named3(segs(h), "packages", "files"), h, hashes(t))

# a pair of a files table as a file
def pair.file(kv: T.Kv) -> K.File:
  T.Kv{k, v} = kv
  K.File{k, v}

# every pair of a files table, as files
def pair.files(ps: List<&2, T.Kv>) -> List<&2, K.File>:
  match ps:
    case []:
      []
    case h <> t:
      pair.file(h) <> pair.files(t)

# the package a lock records under this hash
def pack_of(+ss: List<&2, T.Sect>, +key: String) -> Pack:
  Pack{key, src_of(at3(ss, "packages", key, "source")),
    pair.files(at3(ss, "packages", key, "files"))}

# every package a lock records
def packs.at(+ss: List<&2, T.Sect>, hs: List<&2, String>) -> List<&2, Pack>:
  match hs:
    case []:
      []
    case h <> t:
      pack_of(ss, h) <> packs.at(ss, t)

# every package a lock records
def packs(+ss: List<&2, T.Sect>) -> List<&2, Pack>:
  packs.at(ss, hashes(ss))

# a package's source
def pack.src(package: Pack) -> Src:
  Pack{_h, s, _f} = package
  s

# a package's files
def pack.files(package: Pack) -> List<&2, K.File>:
  Pack{_h, _s, f} = package
  f

# the manifest text a package is served with
def pack.manifest(package: Pack) -> String:
  K.manifest_of(pack.files(package))

# where a package comes from, in a word
def src.kind(source: Src) -> String:
  match source:
    case Hub{}:
      "hub"
    case Git{_u, _r, _e, _ro, _n, _t}:
      "git"

# the commit a package is pinned to, or "" when it comes from the hub
def src.rev(source: Src) -> String:
  match source:
    case Hub{}:
      ""
    case Git{_u, rev, _e, _ro, _n, _t}:
      rev

# the repo a package was vendored from, or "" when it comes from the hub
def src.url(source: Src) -> String:
  match source:
    case Hub{}:
      ""
    case Git{url, _r, _e, _ro, _n, _t}:
      url

# the directory inside a checkout a vendored package's paths are written from
def src.root(source: Src) -> String:
  match source:
    case Hub{}:
      ""
    case Git{_u, _r, _e, root, _n, _t}:
      root

# the NAR hash nix rebuilds a vendored package's checkout by, or "" when it
# comes from the hub
def src.nar(source: Src) -> String:
  match source:
    case Hub{}:
      ""
    case Git{_u, _r, _e, _ro, nar, _t}:
      nar
