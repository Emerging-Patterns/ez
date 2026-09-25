# git/git: what ez asks of git, and how it reads the answers. The decisions are
# pure functions over what `git ls-remote` printed and what a checkout's
# ez.toml says: which tag `ez add` pins (`choose`), what a named ref names
# (`exact`), the default branch (`tip.*`), whether a ref is already a commit
# (`is_rev`), and a package's entry and name (`entry.*`, `called.*`). The
# planners (add/plan.bend, lock/up.bend) make them; the commands that run git
# here are the interpreters', which clone, weigh and ask about ancestry.
#
# Nothing here reimplements git. Bend links no TLS and Base has no readdir, so
# the programs that already speak the protocol are run instead, through the one
# process effect the rest of ez uses: arguments execvp'd, no shell between.
import Base
import ../io/file.bend as F
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P
import ../sha/nar.bend as Nar
import ../ez/say.bend as Say

# one `<sha>\t<name>` row of what `git ls-remote` printed
type Row is Data:
  Row{rev: String, name: String}

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

# a git command that failed stops the command, with whatever git said
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

# a source as git is to read it. A ledger records a local path as it was
# given, relative to the project, which is the directory ez runs in, so the
# ledger reads the same on every clone. git reads such a path from somewhere
# else: a fetch from inside its work directory, and `ls-remote` from the top
# of any repository around it. Every git command here that is handed a source
# is handed this instead.
def anchored(+url: String) -> IO(String):
  do IO<String>:
    +here : String <- R.exec(["pwd"])
    return P.anchor(String.trim(R.text(here)), url)

# the checkout a package is taken from: the pinned commit alone, at the depth
# of one, so a repo with a long history costs nothing to vendor. The fetch is
# quiet; the line above it is what a person sees while it runs.
def clone.say(+work: String, +url: String, +rev: String, +msg: String) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Say.hold(msg)
    +from : String <- anchored(url)
    run("init", ["git", "init", "-q", work])
    run("fetch", ["git", "-C", work, "fetch", "-q", "--depth", "1", from, rev])
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

# a row's ref name
def row.name(line: Row) -> String:
  Row{_rev, name} = line
  name

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
# condition says, so the first row that answered still cost a walk of every
# row after it.
def named.step(here: Bool, rev: String, rest: Unit -> String) -> String:
  match here:
    case True{}:
      rev
    case False{}:
      rest(Unit{})

# the commit of the first row whose ref name is exactly `want`, or "" when no
# row is. The whole name is compared: `git ls-remote` matches its patterns
# against the tail of a ref, so it answers `refs/heads/main` with
# `refs/heads/feature/main` as well, and only this comparison tells them apart.
def named(rs: List<&2, Row>, +want: String) -> String:
  match rs:
    case []:
      ""
    case +h <> t:
      named.step(String.eq(row.name(h), want), row.rev(h), _u => named(t, want))

# the first of two answers that says anything
def or_else(+primary: String, fallback: String) -> String:
  Bool.pick(String, String.is_empty(primary), fallback, primary)

# the commit a ref names, from the rows the remote answered with. A tag comes
# first, through its peeled `^{}` row when it is annotated, since that row is
# the commit and the other is the tag object; then a branch of that name. No
# other row is ever picked, so a tag and a branch that share a name resolve to
# the tag, and `main` never resolves to `feature/main`.
def exact(+rs: List<&2, Row>, +ref: String) -> String:
  or_else(named(rs, "refs/tags/" ++ ref ++ "^{}"),
    or_else(named(rs, "refs/tags/" ++ ref), named(rs, "refs/heads/" ++ ref)))

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

# the first char of a name in upper case, which is how bend writes an alias
def title.go(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case h <> t:
      String.from_list(Char.to_upper(h) <> t)

# a name as an import alias, as `ez add` and `ez publish` print it
def title(text: String) -> String:
  title.go(String.to_list(text))

# the import line a consumer writes for a package: the hash, the entry's path
# inside the package, which is where the hub serves it, and the entry's name
# as the alias, the way bend prints it. `ez add` and `ez publish` both print
# this line.
def import.line(+hash: String, +at: String) -> String:
  "import " ++ hash ++ "/" ++ at ++ " as " ++ title(P.unbend(P.base(at)))

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

# the package name a parsed document gives, or "" when it did not parse
def called.sects(ok: Bool, ss: List<&2, T.Sect>) -> String:
  match ok:
    case False{}:
      ""
    case True{}:
      M.value(M.pairs_of(ss, "package"), "name")

# the package name a parsed document gives
def called.doc(toml: T.Toml) -> String:
  T.Toml{bad, _name, _pairs, sects} = toml
  called.sects(String.is_empty(bad), sects)

# a checkout with no ez.toml gives no package name
def called.maybe(got: Maybe<&2, String>) -> String:
  match got:
    case None{}:
      ""
    case Some{text}:
      called.doc(T.parse(text))

# the entry a vendoring is taken from. One that was asked for is that one.
def entry.for(given: Bool, +entry: String, +work: String) -> IO(String):
  match given:
    case True{}:
      IO.pure(String, entry)
    case False{}:
      entry.at(work)

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
    +from : String <- anchored(url)
    +out : String <- R.exec(["git", "ls-remote", "--symref", from, "HEAD"])
    remote.said(R.ok(out), url, R.text(out))

# a bare clone, blobs left behind. Ancestry only needs the commits. The clone
# is quiet; the line is what shows while it runs.
def clone.bare(+work: String, +url: String) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Say.hold(Say.git.fetch(url))
    +from : String <- anchored(url)
    run("clone", ["git", "clone", "--bare", "--filter=blob:none", "-q", from, work])
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
def descendant.clone(+work: String, +url: String, +pin: String, +tip: String) -> IO(Bool):
  do IO<Bool>:
    _rm : String <- R.exec(["rm", "-rf", work])
    clone.bare(work, url)
    +out : String <- R.exec(["git", "-C", work, "merge-base", "--is-ancestor",
      pin, tip])
    _cl : String <- R.exec(["rm", "-rf", work])
    descendant.code(R.code(out), R.text(out))

# whether `tip` descends from `pin`, the same commit included
def descendant.go(same: Bool, work: String, url: String, pin: String, tip: String) -> IO(Bool):
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

def nums.put(ok: Bool, +part: String, rest: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
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

def ids.ok(ok: Bool, num: Bool, +part: String, rest: Maybe<&2, List<&2, Id>>) -> Maybe<&2, List<&2, Id>>:
  match ok:
    case False{}:
      None{}
    case True{}:
      ids.cons(id.make(num, part), rest)

def ids.put(empty: Bool, ok: Bool, num: Bool, +part: String, rest: Maybe<&2, List<&2, Id>>) -> Maybe<&2, List<&2, Id>>:
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

# a version with no pre-release, which is a release
def release.ver(version: Ver) -> Bool:
  match version:
    case No{}:
      False{}
    case Yes{_ns, ps}:
      List.is_empty(&2, Id, ps)

# a semver-ish tag that is a release: `v1.9.0`, not `v2.0.0-rc1`
def release(+name: String) -> Bool:
  release.ver(ver.of(name))

# a name that is a release, weighed against the greatest release after it the
# way `latest` weighs any two versions; a name that is not is passed over
def latest.rel.step(keep: Bool, +name: String, +rest: String) -> String:
  match keep:
    case False{}:
      rest
    case True{}:
      latest.have(String.is_empty(rest), name, rest, ver.of(name))

# the greatest release, or "" when no name is one
def latest.rel(names: List<&2, String>) -> String:
  match names:
    case Nil{}:
      ""
    case Con{+h, t}:
      latest.rel.step(release(h), h, latest.rel(t))

# one name found to be a release, or the rest still to be asked about
def has.release.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether any name is a release
def has.release(names: List<&2, String>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{+h, t}:
      has.release.step(release(h), _u => has.release(t))

# the greatest release when there is one, and otherwise the greatest of what
# is left, every one of which is a pre-release
def choose.go(none: Bool, +rel: String, +any: String) -> String:
  match none:
    case True{}:
      any
    case False{}:
      rel

# the tag `ez add` pins when no ref was asked for: a release beats every
# pre-release, however much greater the pre-release's numbers are, and
# within each class the greatest wins by `ord.ver`, the later of two equal
# ones winning as `latest` has it. "" when no name is semver-ish.
def choose(+names: List<&2, String>) -> String:
  choose.go(String.is_empty(latest.rel(names)), latest.rel(names), latest(names))


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
