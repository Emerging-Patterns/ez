# git/git: a package that was never published, taken from the repo it lives in.
# `hub/hub` is this job over HTTP; this is the same job over git, and both end
# with the same `0x<hash>` over the same manifest, so a package vendored out of
# a repo keeps its name if upstream ever publishes it.
#
# Nothing here reimplements git. Bend links no TLS and Base has no readdir, so
# the programs that already speak the protocol are run instead, through the one
# process effect the rest of ez uses: arguments execvp'd, no shell between.
import Base
import ../io/file.bend as F
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P
import ../sha/nar.bend as Nar
import ../ez/say.bend as Say

# what a ref turned out to name: the commit that gets pinned, and the tag or
# branch that was asked for, "" when the ref was a commit to begin with
type Ref is Data:
  Ref{rev: String, tag: String}

# one `<sha>\t<name>` row of what `git ls-remote` printed
type Row is Data:
  Row{rev: String, name: String}

# what a vendoring amounts to, which is everything the ledger records: the
# package's `0x` name, where it came from, the commit pinned, the ref asked
# for, and the entry the hash was computed from
type Got is Data:
  Got{hash: String, url: String, rev: String, entry: String, tag: String,
    root: String, nar: String}

# how two versions compare. A release is greater than its prerelease, and a
# numeric identifier is less than a word, which is the semver order.
type Ord is Data:
  Lt{}
  Eq{}
  Gt{}

# one prerelease identifier
type Id is Data:
  IdNum{n: Nat}
  IdWord{s: String}

# a semver-ish tag, or a name that is not one. Build metadata is not kept:
# it does not change which tag is newer.
type Ver is Data:
  No{}
  Yes{nums: List<&2, Nat>, pre: List<&2, Id>}

# a string split once, on the first time a char occurs
type Cut is Data:
  Cut{left: String, right: String}

# a git command that failed stops the command, with whatever git said. Read
# here rather than in `lock/restore.bend`, because both halves of ez's git
# work — vendoring a repo and rebuilding it from the lock — run the same
# commands and must fail the same way.
def ran(ok: Bool, what: String, text: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: git " ++ what ++ ": " ++ text)

# one git command
def run(what: String, args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(args)
    ran(R.ok(out), what, R.text(out))

# the checkout a package is taken from: the pinned commit alone, at the depth
# of one, so a repo with a long history costs nothing to vendor. The fetch is
# quiet; the line above it is what a person sees while it runs.
def clone.say(+work: String, +url: String, +rev: String, +msg: String) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Say.hold(msg)
    run("init", ["git", "init", "-q", work])
    run("fetch", ["git", "-C", work, "fetch", "-q", "--depth", "1", url, rev])
    run("checkout", ["git", "-C", work, "checkout", "-q", rev])
    Say.done(s)

# a shallow clone of one commit into `work`, with a line saying what it fetches
def clone(+work: String, +url: String, +rev: String) -> IO(Unit):
  clone.say(work, url, rev, Say.git.fetch(url))

# one step of a scan looking for one hit, with the head's answer in hand.
# `Bool.or` is an ordinary function and reduces both of its sides, so the
# alphabet was read to its end for every char of every ref. The rest of the
# scan arrives as a thunk, which is a value, and only the arm that wants it
# applies it.
def among.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a char is one of these. Base has `Char.is_digit` and `Char.is_alpha`
# and nothing between, and a commit name is written with neither alphabet but
# with sixteen characters of its own, so the sixteen are named.
def among(+ch: Char, cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +h <> t:
      among.step(Char.is_eq(h, ch), _u => among(ch, t))

# a char a commit name may hold
def hex.at(ch: Char) -> Bool:
  among(ch, String.to_list("0123456789abcdef"))

# one step of the walk, and `among.step` turned around: `Bool.and` reduces
# both of its sides too, so the first char that is not hex still cost a walk
# of the rest of the ref
def hex.all.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether every char of a ref is one. Base's `List.all` applies an erased
# function parameter, which falls outside the termination check; this walk is
# structural.
def hex.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      hex.all.step(hex.at(h), _u => hex.all(t))

# a ref that is already the commit it names, which is what `git rev-parse`
# prints: forty hex characters and nothing else. Such a ref needs no remote
# asked about it, and leaves no tag behind to re-resolve later.
def is_rev(+ref: String) -> Bool:
  Bool.and(Nat.is_eq(String.length(ref), 40n), hex.all(String.to_list(ref)))

# a row's commit
def row.rev(line: Row) -> String:
  Row{rev, _name} = line
  rev

# a row `git ls-remote` wrote for the peeled `^{}` form of a ref, which is the
# commit an annotated tag points at rather than the tag object itself
def row.peeled(line: Row) -> Bool:
  Row{_rev, name} = line
  String.ends_with(name, "^{}")

# one row taken apart. ls-remote separates the two fields with a tab.
def row_of(+text: String) -> Row:
  Row{K.word(String.split(text, '\t'), 0n), K.word(String.split(text, '\t'), 1n)}

# a line that says nothing is no row
def row.put(+text: String) -> List<&2, Row>:
  Bool.pick(List<&2, Row>, String.is_empty(String.trim(text)), [], [row_of(text)])

# every row of what ls-remote printed
def rows(ls: List<&2, String>) -> List<&2, Row>:
  match ls:
    case []:
      []
    case h <> t:
      List.append(&2, Row, row.put(h), rows(t))

# one step of the search, with the head's answer in hand. A recursive call in
# an arm of a `Bool.pick` is not an arm at all: it is built whatever the
# condition says, so the first peeled row still cost a walk of every row after
# it.
def peeled.step(here: Bool, rev: String, rest: Unit -> String) -> String:
  match here:
    case True{}:
      rev
    case False{}:
      rest(Unit{})

# the first peeled row's commit, or "" when no row is peeled
def peeled(rs: List<&2, Row>) -> String:
  match rs:
    case []:
      ""
    case +h <> t:
      peeled.step(row.peeled(h), row.rev(h), _u => peeled(t))

# the first row's commit, or "" when there are none
def unpeeled(rs: List<&2, Row>) -> String:
  match rs:
    case []:
      ""
    case h <> _t:
      row.rev(h)

# the first of two answers that says anything
def or_else(+primary: String, fallback: String) -> String:
  Bool.pick(String, String.is_empty(primary), fallback, primary)

# the commit a ref names: an annotated tag resolves through its peeled row,
# and everything else through the row ls-remote wrote for the ref itself
def pick(+rs: List<&2, Row>) -> String:
  or_else(peeled(rs), unpeeled(rs))

# a ref the remote does not have is a mistake worth naming, since the next
# thing that would happen is a fetch of nothing
def resolve.got(+rev: String, +url: String, +ref: String) -> IO(Ref):
  Bool.pick(IO(Ref), String.is_empty(rev),
    IO.die(Ref, 1, "ez: " ++ url ++ " has no ref named " ++ ref),
    IO.pure(Ref, Ref{rev, ref}))

# what the remote answered about a ref
def resolve.said(ok: Bool, +url: String, +ref: String, +text: String) -> IO(Ref):
  match ok:
    case False{}:
      IO.die(Ref, 1, "ez: git ls-remote " ++ url ++ ": " ++ text)
    case True{}:
      resolve.got(pick(rows(String.lines(text))), url, ref)

# the remote asked what a ref names. Both the ref and its peeled tag form are
# asked for at once, because which of the two exists is the question.
def resolve.ask(+url: String, +ref: String) -> IO(Ref):
  do IO<Ref>:
    +out : String <- R.exec(["git", "ls-remote", url, ref,
      "refs/tags/" ++ ref ++ "^{}"])
    resolve.said(R.ok(out), url, ref, R.text(out))

# a ref that is already a commit needs no remote, with that question already
# answered. Under a `Bool.pick` the whole `git ls-remote` action was built for
# a ref that was never going to ask anything.
def resolve.step(pinned: Bool, url: String, ref: String) -> IO(Ref):
  match pinned:
    case True{}:
      IO.pure(Ref, Ref{ref, ""})
    case False{}:
      resolve.ask(url, ref)

# the commit a ref pins. A tag or a branch is what a person asks for and a
# commit is what gets written down, so both are kept: the commit pins the
# build, and the tag says what an upgrade would re-resolve.
def resolve(+url: String, +ref: String) -> IO(Ref):
  resolve.step(is_rev(ref), url, ref)

# what `git ls-remote --symref` said HEAD was: the commit, and the branch
# that commit is the tip of
type Tip is Data:
  Tip{rev: String, branch: String}

# the rest of the scan only when this row said nothing. A recursive call
# written as an argument of `Bool.pick` would run for a row that already
# answered.
def tip.step(empty: Bool, +got: String, rest: Unit -> String) -> String:
  match empty:
    case True{}:
      rest(Unit{})
    case False{}:
      got

# a HEAD row whose first field is already a commit
def tip.rev.hex(hex: Bool, rev: String) -> String:
  match hex:
    case True{}:
      rev
    case False{}:
      ""

# a HEAD row's commit, or "" when the row is the symref or not HEAD
def tip.rev.pick(head: Bool, hex: Bool, rev: String) -> String:
  match head:
    case False{}:
      ""
    case True{}:
      tip.rev.hex(hex, rev)

# this row's commit when it is HEAD's commit
def tip.rev.at(line: Row) -> String:
  Row{+rev, name} = line
  tip.rev.pick(String.eq(name, "HEAD"), is_rev(rev), rev)

# the commit HEAD names, from the rows `ls-remote --symref` wrote
def tip.rev(rs: List<&2, Row>) -> String:
  match rs:
    case []:
      ""
    case +h <> t:
      tip.step(String.is_empty(tip.rev.at(h)), tip.rev.at(h), _u => tip.rev(t))

# the prefix taken off when it is there, and "" when it is not, so a commit
# line is not mistaken for a branch name
def tip.strip(+text: String, +pre: String) -> String:
  Bool.pick(String, String.starts_with(text, pre),
    String.drop(text, String.length(pre)), "")

# `ref: refs/heads/main` is `main`. Anything else is no branch.
def tip.sym(+rev: String) -> String:
  tip.strip(tip.strip(rev, "ref: "), "refs/heads/")

# the symref only, so the commit row that follows it contributes nothing
def tip.branch.pick(head: Bool, rev: String) -> String:
  match head:
    case False{}:
      ""
    case True{}:
      tip.sym(rev)

# this row's branch when it is the symref for HEAD
def tip.branch.at(line: Row) -> String:
  Row{rev, name} = line
  tip.branch.pick(String.eq(name, "HEAD"), rev)

# the branch HEAD is, or "" when the remote did not say
def tip.branch(rs: List<&2, Row>) -> String:
  match rs:
    case []:
      ""
    case +h <> t:
      tip.step(String.is_empty(tip.branch.at(h)), tip.branch.at(h), _u => tip.branch(t))

# the NAR hash nix rebuilds the checkout by. `fetchgit` hashes the working
# tree with its `.git` taken off, so that is what is weighed here and the
# caller strips `.git` before asking. Computed in Bend; nix is not required.
def nar(+work: String) -> IO(String):
  Nar.path(work)

# the NAR hash of one commit. The checkout is weighed the way `fetchgit`
# weighs it, then removed. Nothing is laid under BEND_LIB.
def weigh(+url: String, +rev: String) -> IO(String):
  +work = ".ez/weigh-" ++ rev
  do IO<String>:
    _rm : String <- R.exec(["rm", "-rf", work])
    _mk : String <- R.exec(["mkdir", "-p", work])
    clone(work, url, rev)
    _dg : String <- R.exec(["rm", "-rf", work ++ "/.git"])
    +s : Say.Spin <- Say.hold(Say.hashing(rev))
    +nh : String <- nar(work)
    Say.done(s)
    _cl : String <- R.exec(["rm", "-rf", work])
    return nh

# a write that did not happen is a failure, not a silence
def wrote(ok: Bool, at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# one file of the package copied where bend will look for it. Copied rather
# than read and written back: the package's identity is its bytes, and a copy
# cannot have an opinion about them.
def place(+from: String, +dst: String, file: K.File) -> IO(Unit):
  +at = K.file.at(file)
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", P.dir(dst ++ "/" ++ at)])
    _cp : String <- R.exec(["cp", P.join(from, at), dst ++ "/" ++ at])
    return Unit{}

# every file of the package
def places(+from: String, +dst: String, fs: List<&2, K.File>) -> IO(Unit):
  match fs:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        place(from, dst, h)
        places(from, dst, t)

# the manifest beside the files, which is the text the `0x` name is the digest
# of and the file bend checks a package against
def manifest(+dst: String, fs: List<&2, K.File>) -> IO(Unit):
  do IO<Unit>:
    ok : Bool <- F.write(dst ++ "/manifest", K.manifest_of(fs))
    wrote(ok, dst ++ "/manifest")

# a package laid out the way the hub serves it, under the name the hub would
# have served it under, so bend resolves the import with no fetch at all
def lay(+lib: String, +hash: String, +from: String, +fs: List<&2, K.File>) -> IO(Unit):
  +dst = lib ++ "/" ++ hash
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", dst])
    places(from, dst, fs)
    manifest(dst, fs)

# a ref that was already a commit leaves no tag behind, and an absent key is
# how `lock/lock.bend` reads that
def origin.tag(+tag: String) -> List<&2, T.Kv>:
  Bool.pick(List<&2, T.Kv>, String.is_empty(tag), [], [T.Kv{"tag", tag}])

# the keys an origin is written with. `lock/lock.bend` reads these six by name
# and `git/LAWS.bend` holds the two halves to each other, so a key renamed on
# one side fails the proof rather than the next lock. The tag arrives already
# made into pairs, because whether there is one is the caller's question and
# the law has to hold either way.
def origin.kvs(url: String, rev: String, entry: String, root: String,
  nar: String, ts: List<&2, T.Kv>) -> List<&2, T.Kv>:
  List.append(&2, T.Kv,
    [T.Kv{"kind", "git"}, T.Kv{"url", url}, T.Kv{"rev", rev},
      T.Kv{"entry", entry}, T.Kv{"root", root}, T.Kv{"narHash", nar}],
    ts)

# the table a package's origin is written in. The hash is quoted because a `0x`
# name is not a bare key, and `lock/lock.bend` reads the name back through the
# same quoting.
def origin.name(hash: String) -> String:
  "origins." ++ T.quote(hash)

# one package's origin as a table
def origin(hash: String, url: String, rev: String, entry: String, root: String,
  nar: String, tag: String) -> T.Sect:
  T.Sect{origin.name(hash),
    origin.kvs(url, rev, entry, root, nar, origin.tag(tag))}

# a table's path, as it was written
def sect.name(section: T.Sect) -> String:
  T.Sect{n, _ps} = section
  n

# a table kept or dropped
def but.put(hit: Bool, section: T.Sect, rest: List<&2, T.Sect>) -> List<&2, T.Sect>:
  match hit:
    case True{}:
      rest
    case False{}:
      section <> rest

# every table but the ones with this path, so vendoring a package again
# replaces what was written for it rather than sitting behind it
def but(ss: List<&2, T.Sect>, +name: String) -> List<&2, T.Sect>:
  match ss:
    case []:
      []
    case +h <> t:
      but.put(String.eq(sect.name(h), name), h, but(t, name))

# the file with this table in it and every other table left as it was. The
# whole document is rendered from the model rather than patched, so what comes
# out is what the parser would read back.
def origins.text(+text: String, +section: T.Sect) -> String:
  T.render(List.append(&2, T.Sect, but(T.sects(T.parse(text)), sect.name(section)),
    [section]))

# where the origins of vendored packages are written down, which is beside the
# BEND_LIB they were vendored into. Named by the half that writes the file;
# `lock/lock.bend` reads it back from here.
def origins.at(lib: String) -> String:
  P.dir(lib) ++ "/origins.toml"

# a package's origin written down, so `ez lock` can say where a package no hub
# has ever seen came from
def note(+lib: String, +section: T.Sect) -> IO(Unit):
  +at = origins.at(lib)
  do IO<Unit>:
    m : Maybe<&2, String> <- F.read(at)
    _mk : String <- R.exec(["mkdir", "-p", P.dir(at)])
    ok : Bool <- F.write(at, origins.text(F.text_of(m), section))
    wrote(ok, at)

# how many components a path has, which is how far down it sits
def depth(path: String) -> Nat:
  List.length(&2, String, String.split(P.norm(path), '/'))

# the directory inside the repo a package's paths are written from. `pkg/pkg`
# resolves that against the checkout it read; the lock records it against the
# repo, so the same number of components is climbed back off the entry's own
# directory here. It is "." until a module reached through `..` re-roots the
# package above the entry.
def root.rel(+at: String, root: String, +entry: String) -> String:
  P.climb(Nat.sub(depth(P.dir(at)), depth(root)), P.dir(entry))

# the entry a package's hash is computed from has to be in the checkout, or
# what was vendored is not the package that was asked for
def have(ok: Bool, +entry: String, +url: String, +rev: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ entry ++ " is not in " ++ url ++ " at " ++ rev)

# the first char of a name in upper case, which is how bend writes an alias
def title.go(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case h <> t:
      String.from_list(Char.to_upper(h) <> t)

# a name as an import alias
def title(text: String) -> String:
  title.go(String.to_list(text))

# the tag a ref resolved through, said out loud, because a person who asked for
# `v1.0` is owed the commit it turned out to be
def said.tag(+tag: String, +rev: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.is_empty(tag), IO.pure(Unit, Unit{}),
    IO.print(tag ++ " is " ++ rev))

# the import line the package is now reachable by, which is what a person does
# next with it
def said(+hash: String, +entry: String, tag: String, rev: String) -> IO(Unit):
  +base = P.base(entry)
  do IO<Unit>:
    said.tag(tag, rev)
    IO.print("import " ++ hash ++ "/" ++ base ++ " as " ++ title(P.unbend(base)))

# the checkout weighed, walked and laid out, once it is on disk
def vendor.tree(+lib: String, +work: String, +url: String, +rev: String,
  +tag: String, +entry: String) -> IO(Got):
  +at = P.join(work, entry)
  do IO<Got>:
    +nh : String <- nar(work)
    +ck : String <- R.exec(["test", "-f", at])
    have(R.ok(ck), entry, url, rev)
    +p : K.Pkg <- K.pkg_of(at)
    +hash : String <- IO.pure(String, K.pkg.hash(p))
    lay(lib, hash, K.pkg.root(p), K.pkg.files(p))
    +rt : String <- IO.pure(String, root.rel(at, K.pkg.root(p), entry))
    note(lib, origin(hash, url, rev, entry, rt, nh, tag))
    said(hash, entry, tag, rev)
    return Got{hash, url, rev, entry, tag, rt, nh}

# `main.bend` when neither the entry nor the bin was named. That is the file
# `ez init` writes when it is not told an entry.
def entry.main(no: Bool, +binary: String) -> String:
  match no:
    case False{}:
      binary
    case True{}:
      "main.bend"

# `bin` only when the package named no entry. The bin is the file a tool
# builds; it is not the entry unless the entry is absent.
def entry.bin(no: Bool, +file: String, +binary: String) -> String:
  match no:
    case False{}:
      file
    case True{}:
      entry.main(String.is_empty(binary), binary)

# the file a package is taken from: its entry, else its bin, else `main.bend`
def entry.pick(+file: String, +binary: String) -> String:
  entry.bin(String.is_empty(file), file, binary)

# a document that did not parse has no entry to take
def entry.sects(ok: Bool, ss: List<&2, T.Sect>) -> String:
  match ok:
    case False{}:
      "main.bend"
    case True{}:
      +ps = M.pairs_of(ss, "package")
      entry.pick(M.value(ps, "entry"), M.value(ps, "bin"))

# the entry a parsed document names
def entry.doc(toml: T.Toml) -> String:
  T.Toml{bad, _name, _pairs, sects} = toml
  entry.sects(String.is_empty(bad), sects)

# the entry a parsed ez.toml names
def entry.text(+text: String) -> String:
  entry.doc(T.parse(text))

# a missing ez.toml names `main.bend`, the same stub `ez init` uses
def entry.maybe(got: Maybe<&2, String>) -> String:
  match got:
    case None{}:
      "main.bend"
    case Some{text}:
      entry.text(text)

# the checkout's ez.toml, read for the entry it names
def entry.at(+work: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(work ++ "/ez.toml")
    return entry.maybe(m)

# the entry a vendoring is taken from. One that was asked for is that one.
def entry.for(given: Bool, +entry: String, +work: String) -> IO(String):
  match given:
    case True{}:
      IO.pure(String, entry)
    case False{}:
      entry.at(work)

# the repo checked out at the pinned commit, and everything that follows from
# it. The `.git` goes before the tree is weighed, because `fetchgit`'s hash is
# over the working tree alone. An entry that was not asked for is read from
# this checkout before that.
def vendor.at(+lib: String, +url: String, ref: Ref, +entry: String) -> IO(Got):
  Ref{+rev, tag} = ref
  +work = lib ++ "/.work-" ++ rev
  do IO<Got>:
    _rm : String <- R.exec(["rm", "-rf", work])
    _mk : String <- R.exec(["mkdir", "-p", work])
    clone(work, url, rev)
    +at : String <- entry.for(Bool.not(String.is_empty(entry)), entry, work)
    _dg : String <- R.exec(["rm", "-rf", work ++ "/.git"])
    g : Got <- vendor.tree(lib, work, url, rev, tag, at)
    _cl : String <- R.exec(["rm", "-rf", work])
    return g

# a package taken from a repo that never published: the ref resolved to a
# commit, the tree checked out at it, the `0x` name computed the way
# `bend <entry> --publish` would have, the files laid out under that name, and
# the origin written down so the lock can rebuild it from the commit alone
def vendor(+lib: String, +url: String, +ref: String, +entry: String) -> IO(Got):
  do IO<Got>:
    r : Ref <- resolve(url, ref)
    vendor.at(lib, url, r, entry)

# a remote with no HEAD is not a repo an upgrade can move
def remote.got(empty: Bool, +rev: String, +branch: String, +url: String) -> IO(Tip):
  match empty:
    case True{}:
      IO.die(Tip, 1, "ez: " ++ url ++ " has no HEAD")
    case False{}:
      IO.pure(Tip, Tip{rev, branch})

# what ls-remote said, or why it said nothing
def remote.said(ok: Bool, +url: String, +text: String) -> IO(Tip):
  match ok:
    case False{}:
      IO.die(Tip, 1, "ez: git ls-remote " ++ url ++ ": " ++ text)
    case True{}:
      +rs = rows(String.lines(text))
      remote.got(String.is_empty(tip.rev(rs)), tip.rev(rs), tip.branch(rs), url)

# HEAD on the remote: the commit the default branch tips, and that branch's
# name. `--symref` is what puts the branch on the line in front of the commit.
def remote(+url: String) -> IO(Tip):
  do IO<Tip>:
    +out : String <- R.exec(["git", "ls-remote", "--symref", url, "HEAD"])
    remote.said(R.ok(out), url, R.text(out))

# a bare clone, blobs left behind. Ancestry only needs the commits. The clone
# is quiet; the line is what shows while it runs.
def clone.bare(+work: String, +url: String) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Say.hold(Say.git.fetch(url))
    run("clone", ["git", "clone", "--bare", "--filter=blob:none", "-q", url, work])
    Say.done(s)

# merge-base answers 0 for a descendant, 1 for anything else, and some other
# status when the question itself could not be asked
def descendant.no(no: Bool, +text: String) -> IO(Bool):
  match no:
    case True{}:
      IO.pure(Bool, False{})
    case False{}:
      IO.die(Bool, 1, "ez: git merge-base: " ++ text)

# the status, read
def descendant.pick(yes: Bool, no: Bool, text: String) -> IO(Bool):
  match yes:
    case True{}:
      IO.pure(Bool, True{})
    case False{}:
      descendant.no(no, text)

# the status a merge-base answered with
def descendant.code(+code: String, +text: String) -> IO(Bool):
  descendant.pick(String.eq(code, "0"), String.eq(code, "1"), text)

# the clone, the question, the clone gone. The same commit is a descendant
# of itself and needs no clone to say so.
def descendant.clone(+work: String, +url: String, +pin: String,
  +tip: String) -> IO(Bool):
  do IO<Bool>:
    _rm : String <- R.exec(["rm", "-rf", work])
    clone.bare(work, url)
    +out : String <- R.exec(["git", "-C", work, "merge-base", "--is-ancestor",
      pin, tip])
    _cl : String <- R.exec(["rm", "-rf", work])
    descendant.code(R.code(out), R.text(out))

# whether `tip` descends from `pin`, the same commit included
def descendant.go(same: Bool, work: String, url: String, pin: String,
  tip: String) -> IO(Bool):
  match same:
    case True{}:
      IO.pure(Bool, True{})
    case False{}:
      descendant.clone(work, url, pin, tip)

# whether `tip` descends from `pin`. `work` is a directory the clone may use.
def descendant.at(+work: String, +url: String, +pin: String, +tip: String) -> IO(Bool):
  descendant.go(String.eq(pin, tip), work, url, pin, tip)

# A tag `ez add` may pin when no ref was asked for. It is semver-ish when,
# after an optional `v`, it is dotted numbers, then an optional prerelease
# of dot-separated identifiers, then optional `+` build metadata. Identifiers
# are letters, digits and hyphens. Comparison is semver: numbers beat lexical
# order, a longer prerelease beats a shorter one that matches up to there,
# and a release beats its prerelease. Anything else is not a candidate.

def ord.lt(lt: Bool) -> Ord:
  match lt:
    case True{}:
      Lt{}
    case False{}:
      Gt{}

def ord.nat(eq: Bool, lt: Bool) -> Ord:
  match eq:
    case True{}:
      Eq{}
    case False{}:
      ord.lt(lt)

def ord.str(eq: Bool, le: Bool) -> Ord:
  match eq:
    case True{}:
      Eq{}
    case False{}:
      ord.lt(le)

def ord.flip(order: Ord) -> Ord:
  match order:
    case Lt{}:
      Gt{}
    case Gt{}:
      Lt{}
    case Eq{}:
      Eq{}

def ord.pad.at(zero: Bool, rest: Unit -> Ord) -> Ord:
  match zero:
    case False{}:
      Lt{}
    case True{}:
      rest(Unit{})

def ord.pad(xs: List<&2, Nat>) -> Ord:
  match xs:
    case Nil{}:
      Eq{}
    case Con{+h, t}:
      ord.pad.at(Nat.is_eq(h, 0n), _u => ord.pad(t))

def ord.nums.at(order: Ord, rest: Unit -> Ord) -> Ord:
  match order:
    case Eq{}:
      rest(Unit{})
    case Lt{}:
      Lt{}
    case Gt{}:
      Gt{}

def ord.nums(left: List<&2, Nat>, right: List<&2, Nat>) -> Ord:
  match left right:
    case Nil{} Nil{}:
      Eq{}
    case Nil{} Con{+h, t}:
      ord.pad(h <> t)
    case Con{+h, t} Nil{}:
      ord.flip(ord.pad(h <> t))
    case Con{+ha, ta} Con{+hb, tb}:
      ord.nums.at(ord.nat(Nat.is_eq(ha, hb), Nat.is_lt(ha, hb)),
        _u => ord.nums(ta, tb))

def ord.id(left: Id, right: Id) -> Ord:
  match left right:
    case IdNum{+n} IdNum{+m}:
      ord.nat(Nat.is_eq(n, m), Nat.is_lt(n, m))
    case IdNum{_n} IdWord{_s}:
      Lt{}
    case IdWord{_s} IdNum{_n}:
      Gt{}
    case IdWord{+s} IdWord{+t}:
      ord.str(String.eq(s, t), String.is_le(s, t))

def ord.ids(left: List<&2, Id>, right: List<&2, Id>) -> Ord:
  match left right:
    case Nil{} Nil{}:
      Eq{}
    case Nil{} Con{_h, _t}:
      Lt{}
    case Con{_h, _t} Nil{}:
      Gt{}
    case Con{ha, ta} Con{hb, tb}:
      ord.nums.at(ord.id(ha, hb), _u => ord.ids(ta, tb))

def ord.rel.at(ae: Bool, be: Bool, left: List<&2, Id>, right: List<&2, Id>) -> Ord:
  match ae be:
    case True{} True{}:
      Eq{}
    case True{} False{}:
      Gt{}
    case False{} True{}:
      Lt{}
    case False{} False{}:
      ord.ids(left, right)

def ord.rel(+left: List<&2, Id>, +right: List<&2, Id>) -> Ord:
  ord.rel.at(List.is_empty(&2, Id, left), List.is_empty(&2, Id, right), left, right)

def ord.ver.at(order: Ord, pa: List<&2, Id>, pb: List<&2, Id>) -> Ord:
  ord.nums.at(order, _u => ord.rel(pa, pb))

def ord.ver(left: Ver, right: Ver) -> Ord:
  match left right:
    case Yes{na, pa} Yes{nb, pb}:
      ord.ver.at(ord.nums(na, nb), pa, pb)
    case No{} _:
      Eq{}
    case Yes{_na, _pa} No{}:
      Eq{}

# a decimal digit's value
def dig(ch: Char) -> Nat:
  U32.to_nat(U32.sub(Char.to_u32(ch), 48))

def num.go(text: String, +acc: Nat) -> Nat:
  match text:
    case SNil{}:
      acc
    case SCon{+h, t}:
      num.go(t, Nat.add(Nat.mul(acc, 10n), dig(h)))

def flag.step(ok: Bool, rest: Unit -> Bool) -> Bool:
  match ok:
    case False{}:
      False{}
    case True{}:
      rest(Unit{})

def digits.go(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      flag.step(Char.is_digit(h), _u => digits.go(t))

def digits.at(empty: Bool, +text: String) -> Bool:
  match empty:
    case True{}:
      False{}
    case False{}:
      digits.go(text)

# a non-empty run of decimal digits
def digits(+text: String) -> Bool:
  digits.at(String.is_empty(text), text)

def nums.cons(value: Nat, rest: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match rest:
    case None{}:
      None{}
    case Some{ns}:
      Some{value <> ns}

def nums.put(ok: Bool, +part: String, rest: Maybe<&2, List<&2, Nat>>) ->
  Maybe<&2, List<&2, Nat>>:
  match ok:
    case False{}:
      None{}
    case True{}:
      nums.cons(num.go(part, 0n), rest)

def nums.of(ps: List<&2, String>) -> Maybe<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Some{[]}
    case Con{+h, t}:
      nums.put(digits(h), h, nums.of(t))

def id.char(+ch: Char) -> Bool:
  Bool.or(Char.is_digit(ch), Bool.or(Char.is_alpha(ch), Char.is_eq(ch, '-')))

def id.chars(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      flag.step(id.char(h), _u => id.chars(t))

def id.make(num: Bool, +text: String) -> Id:
  match num:
    case True{}:
      IdNum{num.go(text, 0n)}
    case False{}:
      IdWord{text}

def ids.cons(ident: Id, rest: Maybe<&2, List<&2, Id>>) -> Maybe<&2, List<&2, Id>>:
  match rest:
    case None{}:
      None{}
    case Some{xs}:
      Some{ident <> xs}

def ids.ok(ok: Bool, num: Bool, +part: String, rest: Maybe<&2, List<&2, Id>>) ->
  Maybe<&2, List<&2, Id>>:
  match ok:
    case False{}:
      None{}
    case True{}:
      ids.cons(id.make(num, part), rest)

def ids.put(empty: Bool, ok: Bool, num: Bool, +part: String,
  rest: Maybe<&2, List<&2, Id>>) -> Maybe<&2, List<&2, Id>>:
  match empty:
    case True{}:
      None{}
    case False{}:
      ids.ok(ok, num, part, rest)

def ids.of(ps: List<&2, String>) -> Maybe<&2, List<&2, Id>>:
  match ps:
    case Nil{}:
      Some{[]}
    case Con{+h, t}:
      ids.put(String.is_empty(h), id.chars(h), digits(h), h, ids.of(t))

def pre.parts(empty: Bool, +raw: String) -> Maybe<&2, List<&2, Id>>:
  match empty:
    case True{}:
      None{}
    case False{}:
      ids.of(String.split(raw, '.'))

def pre.of(had: Bool, +raw: String) -> Maybe<&2, List<&2, Id>>:
  match had:
    case False{}:
      Some{[]}
    case True{}:
      pre.parts(String.is_empty(raw), raw)

def split1.put(ch: Char, cut: Cut) -> Cut:
  Cut{left, right} = cut
  Cut{SCon{ch, left}, right}

def split1.step(hit: Bool, ch: Char, +tail: String, rest: Unit -> Cut) -> Cut:
  match hit:
    case True{}:
      Cut{"", tail}
    case False{}:
      split1.put(ch, rest(Unit{}))

# a string cut at the first of a character, the character dropped; no hit leaves
# the whole string on the left
def split1(+sep: Char, text: String) -> Cut:
  match text:
    case SNil{}:
      Cut{"", ""}
    case SCon{+h, +t}:
      split1.step(Char.is_eq(h, sep), h, t, _u => split1(sep, t))

def unv.step(drop: Bool, ch: Char, tail: String) -> String:
  match drop:
    case True{}:
      tail
    case False{}:
      SCon{ch, tail}

# a tag with one leading `v` or `V` dropped
def unv(text: String) -> String:
  match text:
    case SNil{}:
      ""
    case SCon{+h, t}:
      unv.step(Bool.or(Char.is_eq(h, 'v'), Char.is_eq(h, 'V')), h, t)

def ver.yes(empty: Bool, xs: List<&2, Nat>, ys: List<&2, Id>) -> Ver:
  match empty:
    case True{}:
      No{}
    case False{}:
      Yes{xs, ys}

def ver.pre(+xs: List<&2, Nat>, ps: Maybe<&2, List<&2, Id>>) -> Ver:
  match ps:
    case None{}:
      No{}
    case Some{ys}:
      ver.yes(List.is_empty(&2, Nat, xs), xs, ys)

def ver.nums(had: Bool, ns: Maybe<&2, List<&2, Nat>>, +pre: String) -> Ver:
  match ns:
    case None{}:
      No{}
    case Some{xs}:
      ver.pre(xs, pre.of(had, pre))

def ver.from(empty: Bool, had: Bool, +core: String, +pre: String) -> Ver:
  match empty:
    case True{}:
      No{}
    case False{}:
      ver.nums(had, nums.of(String.split(core, '.')), pre)

def ver.cut(had: Bool, cut: Cut) -> Ver:
  Cut{+core, +pre} = cut
  ver.from(String.is_empty(core), had, core, pre)

def ver.main(+main: String) -> Ver:
  ver.cut(String.contains(main, "-"), split1('-', main))

def ver.core(cut: Cut) -> Ver:
  Cut{+main, _build} = cut
  ver.main(main)

# a tag read as a version. A leading `v` is optional, and `+` metadata is dropped.
def ver.of(+tag: String) -> Ver:
  ver.core(split1('+', unv(tag)))

# whether the first version is strictly newer
def newer(order: Ord) -> Bool:
  match order:
    case Gt{}:
      True{}
    case Lt{}:
      False{}
    case Eq{}:
      False{}

def latest.cmp(take: Bool, +name: String, +rest: String) -> String:
  match take:
    case True{}:
      name
    case False{}:
      rest

def latest.have(empty: Bool, +name: String, +rest: String, version: Ver) -> String:
  match empty:
    case True{}:
      name
    case False{}:
      latest.cmp(newer(ord.ver(version, ver.of(rest))), name, rest)

def latest.step(version: Ver, +name: String, +rest: String) -> String:
  match version:
    case No{}:
      rest
    case Yes{ns, ps}:
      latest.have(String.is_empty(rest), name, rest, Yes{ns, ps})

# the newest semver-ish name, or "" when none of them is one
def latest(names: List<&2, String>) -> String:
  match names:
    case Nil{}:
      ""
    case Con{+h, t}:
      latest.step(ver.of(h), h, latest(t))


# one row's tag name, or nothing when the row is peeled or not a tag
def tag.put(hit: Bool, +name: String) -> List<&2, String>:
  match hit:
    case False{}:
      []
    case True{}:
      [String.drop(name, String.length("refs/tags/"))]

def tag.keep(peeled: Bool, +name: String) -> List<&2, String>:
  match peeled:
    case True{}:
      []
    case False{}:
      tag.put(String.starts_with(name, "refs/tags/"), name)

def tag.one(line: Row) -> List<&2, String>:
  Row{_rev, +name} = line
  tag.keep(String.ends_with(name, "^{}"), name)

# every tag name `ls-remote --tags` wrote, peeled rows left out
def tag.names(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{+h, t}:
      List.append(&2, String, tag.one(h), tag.names(t))

# a row's ref name
def row.name(line: Row) -> String:
  Row{_rev, name} = line
  name

def head.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether the remote advertised this exact ref
def head.has(+want: String, rs: List<&2, Row>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      head.step(String.eq(row.name(h), want), _u => head.has(want, t))

# `master` when it was advertised, and nothing when it was not
def branch.master(has: Bool) -> String:
  match has:
    case True{}:
      "master"
    case False{}:
      ""

# `main` when it was advertised, otherwise `master`
def branch.main(has: Bool, rs: List<&2, Row>) -> String:
  match has:
    case True{}:
      "main"
    case False{}:
      branch.master(head.has("refs/heads/master", rs))

# the branch a default pin uses: `main`, or `master` when `main` is absent
def branch.pick(+rs: List<&2, Row>) -> String:
  branch.main(head.has("refs/heads/main", rs), rs)

def tags.said(ok: Bool, +url: String, +text: String) -> IO(List<&2, String>):
  match ok:
    case False{}:
      IO.die(List<&2, String>, 1, "ez: git ls-remote " ++ url ++ ": " ++ text)
    case True{}:
      IO.pure(List<&2, String>, tag.names(rows(String.lines(text))))

# every tag on the remote
def tags(+url: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["git", "ls-remote", "--tags", url])
    tags.said(R.ok(out), url, R.text(out))

def branch.have(empty: Bool, +name: String, +url: String) -> IO(String):
  match empty:
    case True{}:
      IO.die(String, 1, "ez: " ++ url ++ " has no main or master")
    case False{}:
      IO.pure(String, name)

def heads.said(ok: Bool, +url: String, +text: String) -> IO(String):
  match ok:
    case False{}:
      IO.die(String, 1, "ez: git ls-remote " ++ url ++ ": " ++ text)
    case True{}:
      +name = branch.pick(rows(String.lines(text)))
      branch.have(String.is_empty(name), name, url)

# `main` if the remote has it, otherwise `master`
def heads(+url: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["git", "ls-remote", url, "refs/heads/main",
      "refs/heads/master"])
    heads.said(R.ok(out), url, R.text(out))

def default.go(empty: Bool, +tag: String, +url: String) -> IO(String):
  match empty:
    case False{}:
      IO.pure(String, tag)
    case True{}:
      heads(url)

# the ref `ez add` pins when none was asked for: the latest semver-ish tag,
# or `main`, or `master` when `main` is not there
def default.ref(+url: String) -> IO(String):
  do IO<String>:
    names : List<&2, String> <- tags(url)
    +best : String <- IO.pure(String, latest(names))
    default.go(String.is_empty(best), best, url)
