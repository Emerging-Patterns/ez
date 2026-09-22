# lock/lock: every hub package an import graph reaches, resolved transitively
# and written down. Nix reads the lock and fetches each file as a fixed-output
# derivation, so `bend` never touches the network inside the sandbox.
#
# A package resolves from the hub, or, when it was vendored from a repo that
# never published, from the git rev recorded for it. Both end up as the same
# BEND_LIB tree.
#
# What a lock reads is what a clone has: the ledger, the committed sources,
# the committed trees under `.ez/lib`, each git dependency's files at the rev
# the ledger pins, and hub content, which is checked against its hash. ez.toml
# is the only record of where a package comes from. `ez add` also writes
# .ez/origins.toml, which .gitignore keeps out of the repo, and the lock does
# not read it: a lock that needs a gitignored file is a lock a clone cannot
# reproduce.
import Base
import ../io/file.bend as F
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../sha/sha.bend as Sha
import ../hub/hub.bend as Web
import ../git/git.bend as Git
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P
import ../ez/say.bend as Say

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
def body_of(got: Web.Got) -> IO(String):
  match got:
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
def fetch.one(+hub: String, +hash: String, +item: K.File) -> IO(String):
  do IO<String>:
    g : Web.Got <- Web.fetch(url_of(hub, hash, K.file.at(item)), K.file.sum(item))
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
def disk.one(+lib: String, +hash: String, +item: K.File) -> IO(String):
  +at = url_of(lib, hash, K.file.at(item))
  do IO<String>:
    m : Maybe<&2, String> <- F.read(at)
    +text : String <- IO.pure(String, F.text_of(m))
    disk.judge(String.eq(Sha.hex(text), K.file.sum(item)), at, text)

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

# why an entry is missing from a checkout, or "" when it is there
def entry.why(ok: Bool, +entry: String, +url: String, +rev: String) -> String:
  Bool.pick(String, ok, "", "ez: " ++ entry ++ " is not in " ++ url ++ " at " ++ rev)

# a checkout that failed a check is removed, and the lock stops
def fetch.stop(+work: String, +why: String) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", work])
    IO.die(Unit, 1, why)

# a check that passed lets the fetch go on
def fetch.judge(+why: String, +work: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(why), IO.pure(Unit, Unit{}),
    fetch.stop(work, why))

# a git package whose tree is not under BEND_LIB, fetched at the rev the ledger
# pins with the same shallow clone `ez add` and `ez fetch` use, weighed against
# the ledger's NAR hash, walked from its entry the way `ez add` walked it, and
# laid out under the hash the ledger names, the way `ez fetch` lays it. The
# tree stays there, since the build that follows a lock needs it, and so a
# second lock reads it instead of fetching again.
def fetch.git(+lib: String, +hash: String, +url: String, +rev: String, +entry: String, +nar: String) -> IO(Unit):
  +work = lib ++ "/.work-" ++ hash
  +at = P.join(work, entry)
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", work])
    _mk : String <- R.exec(["mkdir", "-p", work])
    Git.clone.say(work, url, rev, Say.dep.git(Say.label(hash, entry), url))
    _dg : String <- R.exec(["rm", "-rf", work ++ "/.git"])
    +s : Say.Spin <- Say.hold(Say.hashing(rev))
    +got : String <- Git.nar(work)
    Say.done(s)
    fetch.judge(nar.why(nar, got, url, rev), work)
    +ck : String <- R.exec(["test", "-f", at])
    fetch.judge(entry.why(R.ok(ck), entry, url, rev), work)
    +p : K.Pkg <- K.pkg_of(at)
    Git.lay(lib, hash, K.pkg.root(p), K.pkg.files(p))
    _cl : String <- R.exec(["rm", "-rf", work])
    return Unit{}

# a git package always has files, since its entry is one. A manifest that
# names none is not a tree to record, and is refused rather than written as an
# empty `files` table.
def tree.judge(empty: Bool, +at: String) -> IO(Unit):
  match empty:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " names no files")

# a git package's tree, read from BEND_LIB with the manifest beside it
def read.tree(+lib: String, +hash: String, +text: String) -> IO(Body):
  do IO<Body>:
    fs : List<&2, K.File> <- files_of(hash, text)
    +files : List<&2, K.File> <- IO.pure(List<&2, K.File>, fs)
    tree.judge(List.is_empty(&2, K.File, files), url_of(lib, hash, "manifest"))
    srcs : List<&2, String> <- disk.all(lib, hash, files)
    return Body{files, srcs}

# a tree already there is read; a missing one is fetched first. A missing
# tree is never read as a package with no files.
def read.git.seen(
  got: Maybe<&2, String>,
  +lib: String,
  +hash: String,
  +url: String,
  +rev: String,
  +entry: String,
  +nar: String
) -> IO(Body):
  match got:
    case Some{text}:
      read.tree(lib, hash, text)
    case None{}:
      do IO<Body>:
        fetch.git(lib, hash, url, rev, entry, nar)
        m : Maybe<&2, String> <- F.read(url_of(lib, hash, "manifest"))
        read.tree(lib, hash, F.text_of(m))

# a git package: vendored and committed under `.ez/lib`, fetched there by an
# earlier lock or `ez fetch`, or fetched now at the rev the ledger pins
def read.git(+lib: String, +hash: String, +url: String, +rev: String, +entry: String, +nar: String) -> IO(Body):
  do IO<Body>:
    m : Maybe<&2, String> <- F.read(url_of(lib, hash, "manifest"))
    read.git.seen(m, lib, hash, url, rev, entry, nar)

# why a hub package could not be read. One the ledger names is explained the
# way a hub miss always was. One it does not name is said to be unnamed, since
# that, and not the hub, is what a person has to fix.
def hub.why(named: Bool, +hash: String, +hub: String, +url: String, +why: String) -> String:
  match named:
    case True{}:
      Say.hub.explain(hash, url, why)
    case False{}:
      "ez: " ++ hash ++ " is imported, ez.toml does not name it, and the hub at " ++
        hub ++ " did not serve it (" ++ why ++ "). A package taken from git is recorded with `ez add`."

# the manifest, or why the hub did not have it. A 404 names the package and
# the next step; any other miss is the reason the fetch gave.
def read.hub.miss(named: Bool, +hub: String, +hash: String, +url: String, +why: String, spin: Say.Spin) -> IO(Body):
  do IO<Body>:
    Say.done(spin)
    IO.die(Body, 1, hub.why(named, hash, hub, url, why))

# the files, once the manifest arrived and checked
def read.hub.have(+text: String, +hub: String, +hash: String, spin: Say.Spin) -> IO(Body):
  do IO<Body>:
    fs : List<&2, K.File> <- files_of(hash, text)
    +files : List<&2, K.File> <- IO.pure(List<&2, K.File>, fs)
    srcs : List<&2, String> <- fetch.all(hub, hash, files)
    Say.done(spin)
    return Body{files, srcs}

def read.hub.got(named: Bool, got: Web.Got, +hub: String, +hash: String, +url: String, spin: Say.Spin) -> IO(Body):
  match got:
    case Web.Miss{why}:
      read.hub.miss(named, hub, hash, url, why, spin)
    case Web.Have{body}:
      read.hub.have(body, hub, hash, spin)

# a hub package is fetched, manifest first, and every file checked against it
def read.hub(named: Bool, +hub: String, +hash: String) -> IO(Body):
  +url = url_of(hub, hash, "manifest")
  do IO<Body>:
    +s : Say.Spin <- Say.hold(Say.dep.hub(hash))
    g : Web.Got <- Web.fetch(url, want(hash))
    read.hub.got(named, g, hub, hash, url, s)

# a package's files and their text, from wherever it comes from
def read.pkg(hub: String, lib: String, named: Bool, +hash: String, src: Src) -> IO(Body):
  match src:
    case Hub{}:
      read.hub(named, hub, hash)
    case Git{url, rev, entry, _ro, nar, _t}:
      read.git(lib, hash, url, rev, entry, nar)

# the hash a package is recorded under
def pack.hash(package: Pack) -> String:
  Pack{h, _s, _f} = package
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

# whether a package is already resolved
def has(ds: List<&2, Pack>, +wanted: String) -> Bool:
  match ds:
    case []:
      False{}
    case x <> t:
      any.step(String.eq(pack.hash(x), wanted), _u => has(t, wanted))

# a package resolved, and every package it imports queued behind what is left
def resolve.done(
  body: Body,
  hash: String,
  src: Src,
  rest: List<&2, String>,
  done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)
) -> IO(List<&2, Pack>):
  Body{files, srcs} = body
  go(List.append(&2, String, rest, kids(srcs)), Pack{hash, src, files} <> done)

# one package read, then recorded
def resolve.step(
  hub: String,
  lib: String,
  +orgs: List<&2, Origin>,
  +hash: String,
  rest: List<&2, String>,
  done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)
) -> IO(List<&2, Pack>):
  do IO<List<&2, Pack>>:
    +src : Src <- IO.pure(Src, origin(orgs, hash))
    b : Body <- read.pkg(hub, lib, known(orgs, hash), hash, src)
    resolve.done(b, hash, src, rest, done, go)

# a package already resolved is not resolved twice
def resolve.pick(
  hit: Bool,
  hub: String,
  lib: String,
  orgs: List<&2, Origin>,
  hash: String,
  rest: List<&2, String>,
  done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)
) -> IO(List<&2, Pack>):
  match hit:
    case True{}:
      go(rest, done)
    case False{}:
      resolve.step(hub, lib, orgs, hash, rest, done, go)

# one hash off the queue
def resolve.next(
  hub: String,
  lib: String,
  orgs: List<&2, Origin>,
  +hash: String,
  rest: List<&2, String>,
  +done: List<&2, Pack>,
  go: List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)
) -> IO(List<&2, Pack>):
  resolve.pick(has(done, hash), hub, lib, orgs, hash, rest, done, go)

# the next hash of the queue, handed on with what is left of it
def resolve.pop(
  queue: List<&2, String>,
  +done: List<&2, Pack>,
  go: String -> List<&2, String> -> List<&2, Pack> -> IO(List<&2, Pack>)
) -> IO(List<&2, Pack>):
  match queue:
    case []:
      IO.pure(List<&2, Pack>, done)
    case h <> t:
      go(h, t, done)

# every package the queue reaches, each one resolved once. The carrying on
# arrives as a function, since two defs in Bend may not call each other.
def resolve(
  fuel: Nat,
  +hub: String,
  +lib: String,
  +orgs: List<&2, Origin>,
  queue: List<&2, String>,
  done: List<&2, Pack>
) -> IO(List<&2, Pack>):
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
def root.put(+dir: String, +spec: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, K.is_hub(spec), [], [P.join(dir, spec)])

# every module a file imports, as the files to read next
def root.tasks(+dir: String, ms: List<&2, String>) -> List<&2, String>:
  match ms:
    case []:
      []
    case h <> t:
      List.append(&2, String, root.put(dir, h), root.tasks(dir, t))

# what one file of the project adds: the packages it imports, and the files it
# reaches. A file that is not there is passed over, the way a project with a
# stale import still locks.
def root.found(
  +at: String,
  +ms: List<&2, String>,
  st: Seen,
  go: List<&2, String> -> Seen -> IO(List<&2, String>)
) -> IO(List<&2, String>):
  Seen{files, hits} = st
  go(root.tasks(P.dir(at), ms),
    Seen{at <> files, List.append(&2, String, hits, specs(ms))})

# one file of the project, read and scanned
def root.read(+at: String, st: Seen, go: List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    m : Maybe<&2, String> <- F.read(at)
    root.found(at, K.scan.mods(K.scan(F.text_of(m))), st, go)

# a file already read adds nothing
def root.pick(
  hit: Bool,
  at: String,
  st: Seen,
  go: List<&2, String> -> Seen -> IO(List<&2, String>)
) -> IO(List<&2, String>):
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
def seen.holds(xs: List<&2, String>, +needle: String) -> Bool:
  match xs:
    case []:
      False{}
    case +h <> t:
      any.step(String.eq(h, needle), _u => seen.holds(t, needle))

# one file off the queue, skipped when it has been read already
def root.next(+at: String, +st: Seen, go: List<&2, String> -> Seen -> IO(List<&2, String>)) -> IO(List<&2, String>):
  root.pick(seen.holds(seen.files(st), at), at, st, go)

# the next file of the queue, handed on with what is left of it
def root.pop(
  queue: List<&2, String>,
  +st: Seen,
  go: String -> List<&2, String> -> Seen -> IO(List<&2, String>)
) -> IO(List<&2, String>):
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

# the two tables a package is written as
def pack.sects(package: Pack) -> List<&2, T.Sect>:
  Pack{hash, src, files} = package
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

# the lock as a document: what resolved it, then every package it resolved.
# The bend that ran the lock is not recorded: it is not something a clone
# has, and the flake pins the bend a build uses. A lock written before this
# that records one still reads, since nothing reads the key.
def doc(hub: String, ps: List<&2, Pack>) -> List<&2, T.Sect>:
  List.append(&2, T.Sect,
    [T.Sect{"lock", [T.Kv{"version", "2"}, T.Kv{"hub", hub}]}],
    pack.all(pack.sort(ps)))

# the lock as the text written to ez.lock.toml
def render(hub: String, ps: List<&2, Pack>) -> String:
  T.render(doc(hub, ps))

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

# the lock with its tools after the packages. An empty tool list is the
# lock `render` writes, so a ledger with no tools is unchanged.
def render.pick(empty: Bool, hub: String, ps: List<&2, Pack>, ts: List<&2, M.Tool>) -> String:
  match empty:
    case True{}:
      render(hub, ps)
    case False{}:
      T.render(List.append(&2, T.Sect, doc(hub, ps), tool.sects(ts)))

# the same choice, made by matching the list so it is read once
def render.tools(ts: List<&2, M.Tool>, hub: String, ps: List<&2, Pack>) -> String:
  match ts:
    case []:
      render(hub, ps)
    case h <> t:
      render.pick(False{}, hub, ps, h <> t)

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

# an environment variable's text; unset, ""
def env.text(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# where packages live, which is with the project rather than in ~/.bend/lib
def lib.or(+dir: String) -> String:
  Bool.pick(String, String.is_empty(dir), ".ez/lib", dir)

# the BEND_LIB this project pins
def lib() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LIB")
    return lib.or(String.trim(env.text(r)))

# where the ledger is, which is the project root this command was run from
def ledger.at() -> String:
  "ez.toml"

# the lock of a project, resolved from a named ledger and BEND_LIB. The
# ledger's path is a parameter rather than the fixed name, so a test can lock a
# project that is not the one it was started in. The ledger is read once, and
# it alone says where each package comes from, which hub the rest are fetched
# from, and which tools are pinned.
def lock.at(+toml: String, +at: String, entries: List<&2, String>) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(toml)
    +led : M.Read <- IO.pure(M.Read, M.parse(F.text_of(m)))
    +hub : String <- IO.pure(String, M.hub_of(led))
    hs : List<&2, String> <- roots(U32.to_nat(100000), entries, Seen{[], []})
    ps : List<&2, Pack> <- resolve(U32.to_nat(100000), hub, at, ledger.read(led), hs, [])
    return render.tools(M.tools_of(led), hub, ps)

# the lock of a project, from the files it was asked to start at
def lock(entries: List<&2, String>) -> IO(String):
  do IO<String>:
    at : String <- lib()
    lock.at(ledger.at(), at, entries)
