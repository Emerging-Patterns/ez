# lock/lock: every hub package an import graph reaches, resolved transitively
# and written down. Nix reads the lock and fetches each file as a fixed-output
# derivation, so `bend` never touches the network inside the sandbox.
#
# A package resolves from the hub, or, when it was vendored from a repo that
# never published, from the git rev recorded for it. Both end up as the same
# BEND_LIB tree.
#
# Two files record a rev: ez.toml, which is committed, and .ez/origins.toml,
# which `ez add` writes and .gitignore keeps out of the repo. The ledger is the
# authority and the cache is only a cache, because a clone has the first and
# never the second, and a lock that needs a gitignored file is a lock a clone
# cannot reproduce.
import Base
import ../io/file.bend as F
import ../run/run.bend as R
import ../run/bend.bend as Bend
import ../sha/sha.bend as Sha
import ../hub/hub.bend as Web
import ../git/git.bend as Git
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P

# where a package's bytes come from. A hub package needs nothing else; a git
# one pins a commit, the entry its hash was computed from, the directory inside
# the checkout its paths are written from, and the NAR hash nix rebuilds it by.
type Src is Data:
  Hub{}
  Git{url: String, rev: String, entry: String, root: String, nar: String, tag: String}

# a package the lock records
type Pack is Data:
  Pack{hash: String, src: Src, files: List<&2, K.File>}

# a package's origin, as ez.toml or .ez/origins.toml records it
type Origin is Data:
  Origin{hash: String, src: Src}

# a package that was read: its files, and the text of each one, so the walk can
# see what they import
type Body is Data:
  Body{files: List<&2, K.File>, srcs: List<&2, String>}

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
def segs(s: T.Sect) -> List<&2, String>:
  T.Sect{n, _ps} = s
  T.segments(n)

# whether a table's path is these three segments
def is3(+ss: List<&2, String>, a: String, b: String, c: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 3n),
    Bool.and(String.eq(K.word(ss, 0n), a),
      Bool.and(String.eq(K.word(ss, 1n), b), String.eq(K.word(ss, 2n), c))))

# whether a table's path is one segment, this one
def named1(+ss: List<&2, String>, a: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 1n), String.eq(K.word(ss, 0n), a))

# whether a table's path is two segments headed by this one, whatever the
# second is, which is how a table named after a package hash is found
def named2(+ss: List<&2, String>, a: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 2n), String.eq(K.word(ss, 0n), a))

# whether a table's path is three segments, headed and tailed by these, whatever
# the hash between them is
def named3(+ss: List<&2, String>, a: String, c: String) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, ss), 3n),
    Bool.and(String.eq(K.word(ss, 0n), a), String.eq(K.word(ss, 2n), c)))

# the pairs of a table when it is the one asked for, otherwise the rest's
def at.pick(hit: Bool, s: T.Sect, rest: List<&2, T.Kv>) -> List<&2, T.Kv>:
  match hit:
    case True{}:
      T.Sect{_n, ps} = s
      ps
    case False{}:
      rest

# the pairs of the table at this three segment path, or none
def at3(ss: List<&2, T.Sect>, +a: String, +b: String, +c: String) -> List<&2, T.Kv>:
  match ss:
    case []:
      []
    case +h <> t:
      at.pick(is3(segs(h), a, b, c), h, at3(t, a, b, c))

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

# an `[origins."<hash>"]` table as an origin
def origin.put(hit: Bool, s: T.Sect, rest: List<&2, Origin>) -> List<&2, Origin>:
  match hit:
    case True{}:
      T.Sect{n, ps} = s
      Origin{K.word(T.segments(n), 1n), src_of(ps)} <> rest
    case False{}:
      rest

# every origin a .ez/origins.toml records
def origins(ss: List<&2, T.Sect>) -> List<&2, Origin>:
  match ss:
    case []:
      []
    case +h <> t:
      origin.put(named2(segs(h), "origins"), h, origins(t))

# a ledger's dependency as an origin, when it names a repo. A hub dependency
# contributes nothing, because a package no origin names already resolves from
# the hub, and a record saying so would only be a second way to say it.
def ledger.put(git: Bool, +d: M.Dep) -> List<&2, Origin>:
  match git:
    case True{}:
      [Origin{M.dep.hash(d), Git{M.source.url(M.source.dep(d)),
        M.source.rev(M.source.dep(d)), M.dep.entry(d),
        M.source.root(M.source.dep(d)), M.source.nar(M.source.dep(d)),
        M.source.tag(M.source.dep(d))}}]
    case False{}:
      []

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
def ledger.read(r: M.Read) -> List<&2, Origin>:
  match r:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, ds} = m
      ledger.origins(ds)

# the ledger first, the cache behind it. `origin` answers with the first record
# of a hash, so a package ez.toml names resolves from ez.toml however stale
# .ez/origins.toml has become, and a package it does not name still resolves
# from the cache. That is the only order under which a fresh clone, which has
# the ledger and no cache at all, resolves what a working checkout resolves.
def origins.all(led: List<&2, Origin>, cache: List<&2, Origin>) -> List<&2, Origin>:
  List.append(&2, Origin, led, cache)

# this origin's source when the hash matches, otherwise whatever the rest gave
def origin.at(o: Origin, rest: Src, h: String) -> Src:
  Origin{n, s} = o
  Bool.pick(Src, String.eq(n, h), s, rest)

# where a package comes from, which is the hub unless an origin says otherwise
def origin(ds: List<&2, Origin>, +h: String) -> Src:
  match ds:
    case []:
      Hub{}
    case x <> t:
      origin.at(x, origin(t, h), h)

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

# a manifest that names a path outside its own package is refused, the way
# bend refuses one
def files.judge(+bad: String, hash: String, fs: List<&2, K.File>) -> IO(List<&2, K.File>):
  Bool.pick(IO(List<&2, K.File>), String.is_empty(bad),
    IO.pure(List<&2, K.File>, fs),
    IO.die(List<&2, K.File>, 1, "ez: " ++ hash ++ ": its manifest escapes the package (" ++ bad ++ ")"))

# the files a manifest names, once they are known to stay inside the package
def files_of(hash: String, text: String) -> IO(List<&2, K.File>):
  +fs = manifest.files(String.lines(text))
  files.judge(K.escaped(fs), hash, fs)

# what a fetch answered, or the reason it did not
def body_of(g: Web.Got) -> IO(String):
  match g:
    case Web.Miss{why}:
      IO.die(String, 1, "ez: " ++ why)
    case Web.Have{body}:
      IO.pure(String, body)

# a url under the hub
def url_of(+hub: String, +hash: String, at: String) -> String:
  hub ++ "/" ++ hash ++ "/" ++ at

# bend accepts any prefix of the sha256, and a package's `0x` name is the first
# 32 characters of its manifest's digest
def want(+hash: String) -> String:
  String.drop(hash, 2n)

# one file of a hub package, accepted only when it hashes to what the manifest
# says
def fetch.one(+hub: String, +hash: String, +f: K.File) -> IO(String):
  do IO<String>:
    g : Web.Got <- Web.fetch(url_of(hub, hash, K.file.at(f)), K.file.sum(f))
    body_of(g)

# every file of a hub package
def fetch.all(+hub: String, +hash: String, fs: List<&2, K.File>) -> IO(List<&2, String>):
  match fs:
    case []:
      IO.pure(List<&2, String>, [])
    case h <> t:
      do IO<List<&2, String>>:
        rest : List<&2, String> <- fetch.all(hub, hash, t)
        one : String <- fetch.one(hub, hash, h)
        return one <> rest

# a file of a vendored package, read from BEND_LIB and checked against the
# manifest it came with
def disk.judge(ok: Bool, at: String, text: String) -> IO(String):
  match ok:
    case True{}:
      IO.pure(String, text)
    case False{}:
      IO.die(String, 1, "ez: " ++ at ++ " does not match its manifest")

# one file of a vendored package
def disk.one(+lib: String, +hash: String, +f: K.File) -> IO(String):
  +at = url_of(lib, hash, K.file.at(f))
  do IO<String>:
    m : Maybe<&2, String> <- F.read(at)
    +text : String <- IO.pure(String, F.text_of(m))
    disk.judge(String.eq(Sha.hex(text), K.file.sum(f)), at, text)

# every file of a vendored package
def disk.all(+lib: String, +hash: String, fs: List<&2, K.File>) -> IO(List<&2, String>):
  match fs:
    case []:
      IO.pure(List<&2, String>, [])
    case h <> t:
      do IO<List<&2, String>>:
        rest : List<&2, String> <- disk.all(lib, hash, t)
        one : String <- disk.one(lib, hash, h)
        return one <> rest

# a vendored package is already on disk under BEND_LIB, with the manifest ez
# wrote beside it
def read.git(+lib: String, +hash: String) -> IO(Body):
  do IO<Body>:
    m : Maybe<&2, String> <- F.read(url_of(lib, hash, "manifest"))
    fs : List<&2, K.File> <- files_of(hash, F.text_of(m))
    +files : List<&2, K.File> <- IO.pure(List<&2, K.File>, fs)
    srcs : List<&2, String> <- disk.all(lib, hash, files)
    return Body{files, srcs}

# a hub package is fetched, manifest first, and every file checked against it
def read.hub(+hub: String, +hash: String) -> IO(Body):
  do IO<Body>:
    g : Web.Got <- Web.fetch(url_of(hub, hash, "manifest"), want(hash))
    text : String <- body_of(g)
    fs : List<&2, K.File> <- files_of(hash, text)
    +files : List<&2, K.File> <- IO.pure(List<&2, K.File>, fs)
    srcs : List<&2, String> <- fetch.all(hub, hash, files)
    return Body{files, srcs}

# a package's files and their text, from wherever it comes from
def read.pkg(hub: String, lib: String, +hash: String, src: Src) -> IO(Body):
  match src:
    case Hub{}:
      read.hub(hub, hash)
    case Git{_u, _r, _e, _ro, _n, _t}:
      read.git(lib, hash)

# the hash a package is recorded under
def pack.hash(p: Pack) -> String:
  Pack{h, _s, _f} = p
  h

# one step of a scan that is looking for one hit. Both scans in this file want
# it, so it is stated once here.
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

# whether a package is already resolved
def has(ds: List<&2, Pack>, +h: String) -> Bool:
  match ds:
    case []:
      False{}
    case x <> t:
      any.step(String.eq(pack.hash(x), h), _u => has(t, h))

# a package resolved, and every package it imports queued behind what is left
def resolve.done(b: Body, hash: String, src: Src, rest: List<&2, String>,
  done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)) -> IO(List<&2, Pack>):
  Body{files, srcs} = b
  go(List.append(&2, String, rest, kids(srcs)), Pack{hash, src, files} <> done)

# one package read, then recorded
def resolve.step(hub: String, lib: String, orgs: List<&2, Origin>, +hash: String,
  rest: List<&2, String>, done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)) -> IO(List<&2, Pack>):
  do IO<List<&2, Pack>>:
    +src : Src <- IO.pure(Src, origin(orgs, hash))
    b : Body <- read.pkg(hub, lib, hash, src)
    resolve.done(b, hash, src, rest, done, go)

# a package already resolved is not resolved twice
def resolve.pick(hit: Bool, hub: String, lib: String, orgs: List<&2, Origin>,
  hash: String, rest: List<&2, String>, done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)) -> IO(List<&2, Pack>):
  match hit:
    case True{}:
      go(rest, done)
    case False{}:
      resolve.step(hub, lib, orgs, hash, rest, done, go)

# one hash off the queue
def resolve.next(hub: String, lib: String, orgs: List<&2, Origin>, +hash: String,
  rest: List<&2, String>, +done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)) -> IO(List<&2, Pack>):
  resolve.pick(has(done, hash), hub, lib, orgs, hash, rest, done, go)

# the next hash of the queue, handed on with what is left of it
def resolve.pop(queue: List<&2, String>, +done: List<&2, Pack>,
  go: String -> List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)) -> IO(List<&2, Pack>):
  match queue:
    case []:
      IO.pure(List<&2, Pack>, done)
    case h <> t:
      go(h, t, done)

# every package the queue reaches, each one resolved once. The carrying on
# arrives as a function, since two defs in Bend may not call each other.
def resolve(fuel: Nat, +hub: String, +lib: String, +orgs: List<&2, Origin>,
  queue: List<&2, String>, done: List<&2, Pack>) -> IO(List<&2, Pack>):
  match fuel:
    case 0n:
      IO.pure(List<&2, Pack>, done)
    case 1n+f:
      resolve.pop(queue, done, h => t => d =>
        resolve.next(hub, lib, orgs, h, t, d,
          q => d2 => resolve(f, hub, lib, orgs, q, d2)))

# a file of the project, and every hub package it imports
type Seen is Data:
  Seen{files: List<&2, String>, hits: List<&2, String>}

# a module import as the file to read next, or nothing when it names a package
def root.put(+d: String, +spec: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, K.is_hub(spec), [], [P.join(d, spec)])

# every module a file imports, as the files to read next
def root.tasks(+d: String, ms: List<&2, String>) -> List<&2, String>:
  match ms:
    case []:
      []
    case h <> t:
      List.append(&2, String, root.put(d, h), root.tasks(d, t))

# what one file of the project adds: the packages it imports, and the files it
# reaches. A file that is not there is passed over, the way a project with a
# stale import still locks.
def root.found(+at: String, +ms: List<&2, String>, st: Seen,
  go: List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  Seen{files, hits} = st
  go(root.tasks(P.dir(at), ms),
    Seen{at <> files, List.append(&2, String, hits, specs(ms))})

# one file of the project, read and scanned
def root.read(+at: String, st: Seen,
  go: List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    m : Maybe<&2, String> <- F.read(at)
    root.found(at, K.scan.mods(K.scan(F.text_of(m))), st, go)

# a file already read adds nothing
def root.pick(hit: Bool, at: String, st: Seen,
  go: List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  match hit:
    case True{}:
      go([], st)
    case False{}:
      root.read(at, st, go)

# the files a walk has read
def seen.files(st: Seen) -> List<&2, String>:
  Seen{files, _hits} = st
  files

# the packages a walk has seen named
def seen.hits(st: Seen) -> List<&2, String>:
  Seen{_files, hits} = st
  hits

# whether a name is already among the ones a walk has read. Base's
# `List.contains` applies an erased equality, which Bend's termination check
# cannot see through; this scan is structural.
#
# The list grows by one with every file the project walk reads, so this scan
# is the inner half of a quadratic; `any.step` is what lets it stop at the
# name it was looking for instead of reading past it.
def seen.holds(xs: List<&2, String>, +s: String) -> Bool:
  match xs:
    case []:
      False{}
    case +h <> t:
      any.step(String.eq(h, s), _u => seen.holds(t, s))

# one file off the queue, skipped when it has been read already
def root.next(+at: String, +st: Seen,
  go: List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  root.pick(seen.holds(seen.files(st), at), at, st, go)

# the next file of the queue, handed on with what is left of it
def root.pop(queue: List<&2, String>, +st: Seen,
  go: String -> List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  match queue:
    case []:
      IO.pure(List<&2, String>, seen.hits(st))
    case h <> t:
      go(h, t, st)

# every hub package the project's own files import, directly or through one
# another. Local files import local files, so a multi-file project locks every
# package any of its modules reaches.
def roots(fuel: Nat, queue: List<&2, String>, st: Seen) -> IO(List<&2, String>):
  match fuel:
    case 0n:
      IO.pure(List<&2, String>, seen.hits(st))
    case 1n+f:
      root.pop(queue, st, h => t => s =>
        root.next(h, s, more => s2 => roots(f, List.append(&2, String, more, t), s2)))

# a key worth writing, or nothing at all when its value is empty, so an absent
# tag leaves no trace
def kv(key: String, +val: String) -> List<&2, T.Kv>:
  Bool.pick(List<&2, T.Kv>, String.is_empty(val), [], [T.Kv{key, val}])

# the keys a source contributes to the lock
def src.pairs(s: Src) -> List<&2, T.Kv>:
  match s:
    case Hub{}:
      [T.Kv{"kind", "hub"}]
    case Git{url, rev, entry, root, nar, tag}:
      List.concat(&2, T.Kv,
        [[T.Kv{"kind", "git"}], kv("url", url), kv("rev", rev), kv("entry", entry),
         kv("root", root), kv("narHash", nar), kv("tag", tag)])

# a file of a package as a `"<path>" = "<sha256>"` pair
def file.pair(f: K.File) -> T.Kv:
  K.File{at, sum} = f
  T.Kv{at, sum}

# every file of a package, in path order
def file.pairs(fs: List<&2, K.File>) -> List<&2, T.Kv>:
  match fs:
    case []:
      []
    case h <> t:
      file.pair(h) <> file.pairs(t)

# the two tables a package is written as
def pack.sects(p: Pack) -> List<&2, T.Sect>:
  Pack{hash, src, files} = p
  +at = "packages." ++ T.quote(hash)
  [T.Sect{at ++ ".source", src.pairs(src)},
   T.Sect{at ++ ".files", file.pairs(K.files_of(files))}]

# every package, in hash order
def pack.all(ps: List<&2, Pack>) -> List<&2, T.Sect>:
  match ps:
    case []:
      []
    case h <> t:
      List.append(&2, T.Sect, pack.sects(h), pack.all(t))

# packages are written in hash order, so a lock is the same text however it was
# resolved
def pack.le(a: Pack, b: Pack) -> Bool:
  String.is_le(pack.hash(a), pack.hash(b))

# where a package goes among the packages already in order. The rest of the
# insertion is a parameter, because two defs that call each other are not
# allowed.
def pack.ins.put(le: Bool, x: Pack, h: Pack, t: List<&2, Pack>,
  rest: List<&2, Pack>) -> List<&2, Pack>:
  match le:
    case True{}:
      x <> (h <> t)
    case False{}:
      h <> rest

# a package inserted into a list already in hash order
def pack.ins(ps: List<&2, Pack>, +x: Pack) -> List<&2, Pack>:
  match ps:
    case []:
      [x]
    case Con{+h, +t}:
      pack.ins.put(pack.le(x, h), x, h, t, pack.ins(t, x))

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

# the lock as a document: what resolved it, then every package it resolved
def doc(hub: String, ver: String, ps: List<&2, Pack>) -> List<&2, T.Sect>:
  List.append(&2, T.Sect,
    [T.Sect{"lock", [T.Kv{"version", "2"}, T.Kv{"hub", hub}, T.Kv{"bend", ver}]}],
    pack.all(pack.sort(ps)))

# the lock as the text written to ez.lock.toml
def render(hub: String, ver: String, ps: List<&2, Pack>) -> String:
  T.render(doc(hub, ver, ps))

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
def hash.put(hit: Bool, s: T.Sect, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      T.Sect{n, _ps} = s
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
def pack_of(+ss: List<&2, T.Sect>, +h: String) -> Pack:
  Pack{h, src_of(at3(ss, "packages", h, "source")),
    pair.files(at3(ss, "packages", h, "files"))}

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
def pack.src(p: Pack) -> Src:
  Pack{_h, s, _f} = p
  s

# a package's files
def pack.files(p: Pack) -> List<&2, K.File>:
  Pack{_h, _s, f} = p
  f

# the manifest text a package is served with
def pack.manifest(p: Pack) -> String:
  K.manifest_of(pack.files(p))

# where a package comes from, in a word
def src.kind(s: Src) -> String:
  match s:
    case Hub{}:
      "hub"
    case Git{_u, _r, _e, _ro, _n, _t}:
      "git"

# the commit a package is pinned to, or "" when it comes from the hub
def src.rev(s: Src) -> String:
  match s:
    case Hub{}:
      ""
    case Git{_u, rev, _e, _ro, _n, _t}:
      rev

# the repo a package was vendored from, or "" when it comes from the hub
def src.url(s: Src) -> String:
  match s:
    case Hub{}:
      ""
    case Git{url, _r, _e, _ro, _n, _t}:
      url

# the directory inside a checkout a vendored package's paths are written from
def src.root(s: Src) -> String:
  match s:
    case Hub{}:
      ""
    case Git{_u, _r, _e, root, _n, _t}:
      root

# the NAR hash nix rebuilds a vendored package's checkout by, or "" when it
# comes from the hub
def src.nar(s: Src) -> String:
  match s:
    case Hub{}:
      ""
    case Git{_u, _r, _e, _ro, nar, _t}:
      nar

# where the hub is, which is where bend's own is unless BEND_HUB says otherwise
def hub.or(+s: String) -> String:
  Bool.pick(String, String.is_empty(s), "https://hub.bend-lang.com", s)

# an environment variable's text; unset, ""
def env.text(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# the hub packages are fetched from
def hub() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_HUB")
    return hub.or(String.trim(env.text(r)))

# where packages live, which is with the project rather than in ~/.bend/lib
def lib.or(+s: String) -> String:
  Bool.pick(String, String.is_empty(s), ".ez/lib", s)

# the BEND_LIB this project pins
def lib() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LIB")
    return lib.or(String.trim(env.text(r)))

# the origins recorded beside a BEND_LIB. The file's name belongs to the half
# that writes it, so it is asked for rather than spelled again here.
#
# It is a cache and nothing more. `ez add` writes it as it vendors and
# .gitignore keeps it out of the repo, so a clone never sees one; the ledger
# answers first for every package it names, and this file only for one the
# ledger has forgotten.
def origins_of(+lib: String) -> IO(List<&2, Origin>):
  do IO<List<&2, Origin>>:
    m : Maybe<&2, String> <- F.read(Git.origins.at(lib))
    return origins(T.sects(T.parse(F.text_of(m))))

# where the ledger is, which is the project root this command was run from
def ledger.at() -> String:
  "ez.toml"

# the origins the committed ledger records
def ledger_of(+at: String) -> IO(List<&2, Origin>):
  do IO<List<&2, Origin>>:
    m : Maybe<&2, String> <- F.read(at)
    return ledger.read(M.parse(F.text_of(m)))

# the version of bend that resolved a lock, for the record
def version() -> IO(String):
  do IO<String>:
    +out : String <- Bend.version()
    return K.word(K.words(String.trim(R.text(out))), 1n)

# the lock of a project, resolved against a named hub, ledger and BEND_LIB. The
# ledger's path is a parameter rather than the fixed name, so a test can lock a
# project that is not the one it was started in.
def lock.at(+hub: String, +toml: String, +at: String,
  entries: List<&2, String>) -> IO(String):
  do IO<String>:
    led : List<&2, Origin> <- ledger_of(toml)
    cache : List<&2, Origin> <- origins_of(at)
    +orgs : List<&2, Origin> <- IO.pure(List<&2, Origin>, origins.all(led, cache))
    hs : List<&2, String> <- roots(U32.to_nat(100000), entries, Seen{[], []})
    ps : List<&2, Pack> <- resolve(U32.to_nat(100000), hub, at, orgs, hs, [])
    ver : String <- version()
    return render(hub, ver, ps)

# the lock of a project, from the files it was asked to start at
def lock(entries: List<&2, String>) -> IO(String):
  do IO<String>:
    at : String <- lib()
    h : String <- hub()
    lock.at(h, ledger.at(), at, entries)
