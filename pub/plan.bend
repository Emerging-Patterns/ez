# pub/plan: the planner for `ez publish`, pure. It reads a World
# (pub/world.bend) and either asks the questions still open or makes the plan.
# The package is sent to the hub by `bend --publish`, which is the only thing
# that can send it, but the `0x` name ez reports is the one the package walk
# (`pkg/pkg.bend`) computed from the files, never the one bend printed.
# Reading bend's output is a check, not a lookup: ez already knows the answer
# before bend runs, and what bend says is compared against it.
#
# Publishing is irreversible and public, so every check that can be made
# before the upload is made first, in this order: there is a ledger that
# parses, and it names the entry, and the name it publishes under, if any, is
# one bend takes (EZ-PUB-3); git answers `git status --porcelain
# --untracked-files=normal` about the project and names no path (EZ-PUB-1);
# the walk from the entry makes a package; git tracks every file of that
# package; and the hub the ledger names has every hub package the package
# imports (EZ-PUB-5). Only then is the upload asked for, and its answer is checked
# against ez's hash (EZ-PUB-2). bend cannot report a package's hash without
# uploading it, so that check comes after the upload, and a disagreement
# exits 1 with no import line rather than taking the upload back.
#
# Each stage of `decide` reads what it needs from the World itself rather
# than from the stage before, so a law about one stage holds of every World
# whatever the others say.
import Base
import ../lock/plan.bend as P
import ../tool/world.bend as TW
import ../ledger/manifest.bend as M
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as G
import ./world.bend as PW
import ./blurb.bend as B
import ../lock/lock.bend as L
import ../sha/sha.bend as Sha
import ../io/file.bend as F

# ---------------------------------------------------------------------------
# bend's answer

# how many characters a `0x` name is written with: the two of the prefix and
# the thirty-two `pkg/pkg.bend`'s `hash_of` takes off a sha256
def name.length() -> Nat:
  34n

# whether a line is a `0x` package name and nothing else. Anchored at both
# ends: the prefix, the exact length, and every character after the prefix one
# a lowercase hex digest may hold. `git/git.bend` already walks a hex string
# for `is_rev`, and its walk stops at the first character that is not hex.
#
# The lines bend prints around its answer fail this, and `pub/LAWS.bend` says
# so for the two that hold the name, rather than leaving it to a reading of
# bend's source: `publishing N files, ... as 0x... (mining its proof of work)`
# and `import 0x.../entry.bend as Name` each start with something that is not
# `0x`. The terms notice and the license line bend 2.0.27 prints first
# (`Publishing to BendHub: ...`, `License: ...`) start with a word too.
def is_name(+word: String) -> Bool:
  Bool.and(String.starts_with(word, "0x"),
    Bool.and(Nat.is_eq(String.length(word), name.length()),
      G.hex.all(String.to_list(String.drop(word, 2n)))))

# one line of bend's output weighed. A line that is a name must be ours, and
# makes the rest of the walk one that has seen a name; any other line is
# passed over. `Bool.and` builds both of its sides, so the rest of the walk
# arrives as a function of whether a name was seen and is applied once.
def agrees.step(name: Bool, same: Bool, seen: Bool, rest: Bool -> Bool) -> Bool:
  match name:
    case True{}:
      Bool.and(same, rest(True{}))
    case False{}:
      rest(seen)

# whether bend's output, from this line on, agrees with ez's hash, `seen`
# saying whether a line before it was a name
def agrees.go(+ours: String, ls: List<&2, String>, seen: Bool) -> Bool:
  match ls:
    case []:
      seen
    case +h <> t:
      agrees.step(is_name(h), String.eq(ours, h), seen,
        s => agrees.go(ours, t, s))

# whether bend's output agrees with ez's hash: at least one line is a `0x`
# name, and every line that is one is ez's hash. There is no second pattern
# behind this one. An output with no bare name answers nothing, and one that
# names two packages names one that is not ours, whichever it names first.
def agrees(+ours: String, ls: List<&2, String>) -> Bool:
  agrees.go(ours, ls, False{})

# the first line that is a `0x` name and not ours, "" when there is none
def other.step(odd: Bool, line: String, rest: Unit -> String) -> String:
  match odd:
    case True{}:
      line
    case False{}:
      rest(Unit{})

# the walk that finds it, one line at a time
def other(+ours: String, ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      other.step(Bool.and(is_name(h), Bool.not(String.eq(ours, h))), h,
        _u => other(ours, t))

# ---------------------------------------------------------------------------
# the working tree

# one line of `git status --porcelain` weighed, with the rest of the walk
# behind a thunk so a status that names a hundred files stops at the first.
# Every line git prints there names a path whose state on disk is not the
# state the commit holds, so every one of them counts, whatever its two-letter
# code says, `??` for an untracked file included.
def dirty.step(blank: Bool, rest: Unit -> Bool) -> Bool:
  match blank:
    case True{}:
      rest(Unit{})
    case False{}:
      True{}

# whether any line of the status says anything. The only empty line git status
# ever produces is the one `String.lines` makes of the trailing newline, so an
# empty line is the absence of a change rather than a change with no name.
def dirty.lines(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      False{}
    case +h <> t:
      dirty.step(String.is_empty(h), _u => dirty.lines(t))

# one line of the other walk, the same way round
def blanks.step(blank: Bool, rest: Unit -> Bool) -> Bool:
  match blank:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether the status named nothing. Stated as its own walk rather than as the
# negation of the one above, so `pub/LAWS.bend` can hold the two to each other:
# a tree is clean exactly when git named no path at all.
def blanks(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case +h <> t:
      blanks.step(String.is_empty(h), _u => blanks(t))

# whether `git status --porcelain` named a path. Ignored files are not named,
# and that is the project's call, written in its own `.gitignore`: `.ez/` and
# `bin/` hold build output that no commit should. What the package itself
# holds is checked apart from this (`stray` below), so an ignored file the
# entry imports is refused there.
def dirty(text: String) -> Bool:
  dirty.lines(String.lines(text))

# ---------------------------------------------------------------------------
# the name a package is published under

# one character of a version: a digit or a dot
def semver.char(+ch: Char) -> Bool:
  Bool.or(Char.is_digit(ch), Char.is_eq(ch, '.'))

# whether every character of a version is a digit or a dot. A pre-release
# (`1.0.0-rc.1`) or build (`1.0.0+abc`) suffix holds a character that is
# neither, so this is where one is refused, whatever follows it.
def semver.chars(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      +rest = semver.chars(t)
      Bool.and(semver.char(h), rest)

# whether a version is MAJOR.MINOR.PATCH: digits and dots only, and three
# numbers, none with a leading zero (`K.ver.num`, the rule bend's NAMED
# holds each of its four numbers to)
def semver(+text: String) -> Bool:
  +ps = String.split(text, '.')
  Bool.and(semver.chars(text),
    Bool.and(Nat.is_eq(List.length(&2, String, ps), 3n), K.ver.nums(ps)))

# how the ledger names the package on the hub: not at all, so it is
# published by its hash alone; by `<name>@<version>`, as bend's `--publish`
# takes it; or in a way ez refuses, and why
type Named is Data:
  ByHash{}
  ByName{nv: String}
  Unnamed{why: String}

# why a `publish-as` with no `version` is refused
def why.nover(+name: String) -> String:
  "ez: ez.toml's [package] has publish-as = \"" ++ name ++ "\" and no version; " ++
    "a named publish needs both, and one with neither publishes by hash"

# why a `version` with no `publish-as` is refused
def why.noname(+ver: String) -> String:
  "ez: ez.toml's [package] has version = \"" ++ ver ++ "\" and no publish-as; " ++
    "a named publish needs both, and one with neither publishes by hash"

# why a `publish-as` the hub would not take is refused
def why.name(+name: String) -> String:
  "ez: publish-as = \"" ++ name ++ "\" is not a hub name: a lowercase letter, " ++
    "then a-z, 0-9 and -, 12 to 64 characters in all"

# why a `version` that is not MAJOR.MINOR.PATCH is refused
def why.ver(+ver: String) -> String:
  "ez: version = \"" ++ ver ++ "\" is not MAJOR.MINOR.PATCH: three numbers " ++
    "with no leading zeros and no pre-release or build suffix, which ez " ++
    "publishes as bend's four-part MAJOR.MINOR.PATCH.0"

# both keys given: the name first, then the version, then the name bend is
# asked for, the version with bend's fourth number, `0`, after it
def naming.both(name: Bool, ver: Bool, +pa: String, +pv: String) -> Named:
  match name:
    case False{}:
      Unnamed{why.name(pa)}
    case True{}:
      match ver:
        case False{}:
          Unnamed{why.ver(pv)}
        case True{}:
          ByName{pa ++ "@" ++ pv ++ ".0"}

# which of the two keys the ledger gives. Neither is a publish by hash, as
# before the keys existed; one without the other is refused rather than
# guessed at, as `cargo publish` refuses a package with no version.
def naming.go(noname: Bool, nover: Bool, +pa: String, +pv: String) -> Named:
  match noname:
    case True{}:
      match nover:
        case True{}:
          ByHash{}
        case False{}:
          Unnamed{why.noname(pv)}
    case False{}:
      match nover:
        case True{}:
          Unnamed{why.nover(pa)}
        case False{}:
          naming.both(K.name.part(pa), semver(pv), pa, pv)

# how `publish-as` and `version` name the package
def naming(+pa: String, +pv: String) -> Named:
  naming.go(String.is_empty(pa), String.is_empty(pv), pa, pv)

# ---------------------------------------------------------------------------
# the ledger

# what the ledger says: the entry it names and how the package is named on
# the hub, by its hash or by a `<name>@<version>`, or why there is none
type Led is Data:
  Led{entry: String, named: Named}
  LedNo{why: String}

# the entry, with the name the package goes under, or why it goes under none
def led.named(+entry: String, got: Named) -> Led:
  match got:
    case ByHash{}:
      Led{entry, ByHash{}}
    case ByName{nv}:
      Led{entry, ByName{nv}}
    case Unnamed{why}:
      LedNo{why}

# the entry a parsed ledger names, `main.bend` when it names none, and the
# name its `publish-as` and `version` give it
def led.read(ledger: M.Read) -> Led:
  match ledger:
    case M.Bad{why}:
      LedNo{"ez: " ++ M.show(M.Bad{why})}
    case M.Good{m}:
      M.Manifest{_n, +e, _b, _h, +pa, +pv, _ds, _ts} = m
      led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), naming(pa, pv))

# the ledger read. With no ez.toml there is no package, and nothing is
# guessed in its place (`cargo publish` refuses a directory with no
# Cargo.toml the same way).
def led.of(got: Maybe<&2, String>) -> Led:
  match got:
    case None{}:
      LedNo{"ez: no " ++ PW.toml() ++ " here; ez publish sends the package " ++
        "a project's ledger names, and ez init makes one"}
    case Some{text}:
      led.read(M.parse(text))

# what the World's ledger says
def led(world: PW.World) -> Led:
  led.of(PW.ledger(world))

# the entry, as the walk takes it, "" when the ledger names none
def entry.of(ledger: Led) -> String:
  match ledger:
    case Led{e, _nv}:
      Path.norm(e)
    case LedNo{_why}:
      ""

# how the package goes on the hub; a ledger that names no entry sends
# nothing, so it is taken for one that goes by hash
def named.of(ledger: Led) -> Named:
  match ledger:
    case Led{_e, got}:
      got
    case LedNo{_why}:
      ByHash{}

# how a World's package goes on the hub
def named(world: PW.World) -> Named:
  named.of(led(world))

# the `<name>@<version>` the upload names the package by, "" for none
def named.word(got: Named) -> String:
  match got:
    case ByName{nv}:
      nv
    case ByHash{}:
      ""
    case Unnamed{_why}:
      ""

# the entry of a World
def entry(world: PW.World) -> String:
  entry.of(led(world))

# ---------------------------------------------------------------------------
# git status

# what `git status` said of the project, still to ask, or why it said
# nothing
type Status is Data:
  Said{text: String}
  StatusWait{}
  StatusNo{why: String}

# the question: what git says of the directory the project is in
def locate(world: PW.World) -> PW.Ask:
  PW.Tool{TW.Locate{PW.here(world)}}

# a status that git answered, or the command stopped with what git said. A
# directory that is not in a git repository has no commit for what goes to
# the hub to exist in, so it is refused rather than taken for clean.
def status.ran(ok: Bool, +text: String) -> Status:
  match ok:
    case True{}:
      Said{text}
    case False{}:
      StatusNo{"ez: git status: " ++ text}

def status.told(got: TW.Answer) -> Status:
  match got:
    case TW.Located{_abs, _top, _head, ok, text}:
      status.ran(ok, text)
    case TW.Miss{why}:
      StatusNo{why}
    case _:
      StatusNo{"ez: git was not asked about the project"}

def status.answer(got: PW.Answer) -> Status:
  match got:
    case PW.Told{t}:
      status.told(t)
    case PW.Ran{_ok, _text}:
      StatusNo{"ez: git was not asked about the project"}

def status.of(got: PW.Heard) -> Status:
  match got:
    case PW.Open{}:
      StatusWait{}
    case PW.Heard{a}:
      status.answer(a)

# what git status said of the project
def status(+world: PW.World) -> Status:
  status.of(PW.heard(world, locate(world)))

# ---------------------------------------------------------------------------
# the package

# a file the walk asked for, added to what it is given: its text, or gone
# when there is none
def tree.told(got: TW.Answer, +path: String, rest: K.Tree) -> K.Tree:
  match got:
    case TW.Text{m}:
      K.tree.add(m, rest, path)
    case _:
      K.tree.gone(rest, path)

def tree.read(got: PW.Answer, +path: String, rest: K.Tree) -> K.Tree:
  match got:
    case PW.Told{t}:
      tree.told(t, path, rest)
    case PW.Ran{_ok, _text}:
      K.tree.gone(rest, path)

def tree.tool(ask: TW.Ask, got: PW.Answer, rest: K.Tree) -> K.Tree:
  match ask:
    case TW.Read{path}:
      tree.read(got, path, rest)
    case _:
      rest

def tree.one(ask: PW.Ask, got: PW.Answer, rest: K.Tree) -> K.Tree:
  match ask:
    case PW.Tool{q}:
      tree.tool(q, got, rest)
    case _:
      rest

# every file read so far, as the walk is given them: not a whole checkout, so
# a file not read yet is a question
def tree.of(rs: List<&2, PW.Reply>) -> K.Tree:
  match rs:
    case []:
      K.Tree{False{}, [], []}
    case PW.Reply{ask, got} <> t:
      tree.one(ask, got, tree.of(t))

# the files the walk has been given
def tree(world: PW.World) -> K.Tree:
  tree.of(PW.replies(world))

# the walk's fuel: one step for the entry and one per line of the files it
# was given, since every import it can queue is a line of one of them
def fuel(fs: List<&2, K.Source>) -> Nat:
  match fs:
    case []:
      1n
    case K.Source{_at, text} <> t:
      (List.length(&2, String, String.lines(text)) + fuel(t) : Nat)

def fuel.of(tr: K.Tree) -> Nat:
  K.Tree{_whole, fs, _gone} = tr
  fuel(fs)

# the package the entry is published as, over the files read so far
def walked(+world: PW.World) -> K.Walked:
  K.of.tree(fuel.of(tree(world)), entry(world), tree(world))

# the package's hash, "" while there is none
def hash.of(got: K.Walked) -> String:
  match got:
    case K.Walked{h, _root, _fs, _sums}:
      h
    case K.Asks{_at}:
      ""
    case K.Refused{_why}:
      ""

# the hash ez computed for the package
def hash(+world: PW.World) -> String:
  hash.of(walked(world))

# the directory the package's paths are written from, "." for the project's
def root.of(got: K.Walked) -> String:
  match got:
    case K.Walked{_h, root, _fs, _sums}:
      root
    case K.Asks{_at}:
      "."
    case K.Refused{_why}:
      "."

# the entry's path inside the package, which is where the hub serves it: the
# entry's name, under the directories the package re-rooted above it when an
# import climbs out of the entry's directory
def at(+world: PW.World) -> String:
  K.inside(root.of(walked(world)), entry(world))

# the files of a package, as paths of the project
def paths(+root: String, fs: List<&2, K.Source>) -> List<&2, String>:
  match fs:
    case []:
      []
    case K.Source{at, _text} <> t:
      Path.join(root, at) <> paths(root, t)

# ---------------------------------------------------------------------------
# what git tracks

# whether `git ls-files -v` names a path as tracked in the ordinary way. `H`
# is a file git holds and watches; a file marked `--assume-unchanged` (`h`) or
# `--skip-worktree` (`S`) is one whose changes `git status` does not report,
# so its text on disk need not be the commit's, and it counts as untracked.
def tracked.step(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

def tracked.has(ls: List<&2, String>, +path: String) -> Bool:
  match ls:
    case []:
      False{}
    case +h <> t:
      tracked.step(String.eq(h, "H " ++ path), _u => tracked.has(t, path))

# the first path of the package that git does not track, "" when every one
# is tracked
def stray.step(kept: Bool, +path: String, rest: Unit -> String) -> String:
  match kept:
    case True{}:
      rest(Unit{})
    case False{}:
      path

def stray.first(+ls: List<&2, String>, ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case +h <> t:
      stray.step(tracked.has(ls, h), h, _u => stray.first(ls, t))

# what git said of the package's files: every one tracked, the first one it
# does not track, still to ask, or why it said nothing
type Kept is Data:
  Kept{}
  Stray{path: String}
  KeptWait{}
  KeptNo{why: String}

def kept.of(+first: String) -> Kept:
  Bool.pick(Kept, String.is_empty(first), Kept{}, Stray{first})

def kept.ran(ok: Bool, +text: String, +ps: List<&2, String>) -> Kept:
  match ok:
    case True{}:
      kept.of(stray.first(String.lines(text), ps))
    case False{}:
      KeptNo{"ez: git ls-files: " ++ text}

def kept.answer(got: PW.Answer, +ps: List<&2, String>) -> Kept:
  match got:
    case PW.Ran{ok, text}:
      kept.ran(ok, text, ps)
    case PW.Told{_t}:
      KeptNo{"ez: git was not asked what it tracks"}

def kept.heard(got: PW.Heard, +ps: List<&2, String>) -> Kept:
  match got:
    case PW.Open{}:
      KeptWait{}
    case PW.Heard{a}:
      kept.answer(a, ps)

def kept.walked(got: K.Walked, +world: PW.World) -> Kept:
  match got:
    case K.Walked{_h, +root, fs, _sums}:
      kept.heard(PW.heard(world, PW.Tracked{}), paths(root, fs))
    case K.Asks{_at}:
      KeptNo{"ez: the package was not walked"}
    case K.Refused{why}:
      KeptNo{why}

# whether git tracks every file of the package. An ignored file the entry
# imports is one `git status` never names, and one the upload would send
# though no commit holds it, so it is refused here.
def stray(+world: PW.World) -> Kept:
  kept.walked(walked(world), world)

# ---------------------------------------------------------------------------
# the upload

# the words the upload runs: the entry, and after `--publish` the
# `<name>@<version>` the package goes under when it has one, which is how
# bend 2.0.27 publishes and names a package in one run (`bend <file>
# --publish <name>@<version>`). With no name it is the upload by hash alone.
def upload.go(bare: Bool, +entry: String, +named: String) -> List<&2, String>:
  match bare:
    case True{}:
      ["bend", entry, "--publish"]
    case False{}:
      ["bend", entry, "--publish", named]

def upload.line(+entry: String, +named: String) -> List<&2, String>:
  upload.go(String.is_empty(named), entry, named)

# the files of a package, with their texts, at the paths the hub holds them
# at; none while there is no package
def files.of(got: K.Walked) -> List<&2, K.Source>:
  match got:
    case K.Walked{_h, _root, fs, _sums}:
      fs
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# what is said just before the upload: the line the hub will describe the
# package by (`B.blurb`). A package whose first file opens with `import Base`
# would be listed that way for good, so the author sees the line while the
# upload can still be stopped.
def said(+world: PW.World) -> String:
  "hub description: " ++ B.blurb(files.of(walked(world)))

# the question: the entry sent, under the name the ledger gives it, with the
# line said before it
def upload(+world: PW.World) -> PW.Ask:
  PW.Upload{entry(world), named.word(named(world)), said(world)}

# the upload's answer, looked up
def uploaded(+world: PW.World) -> PW.Heard:
  PW.heard(world, upload(world))

# whether an upload's answer agrees with ez's hash: bend exited 0, and its
# output agrees (`agrees`)
def agreed.answer(got: PW.Answer, +ours: String) -> Bool:
  match got:
    case PW.Ran{ok, text}:
      Bool.and(ok, agrees(ours, String.lines(text)))
    case PW.Told{_t}:
      False{}

def agreed.of(got: PW.Heard, +ours: String) -> Bool:
  match got:
    case PW.Open{}:
      False{}
    case PW.Heard{a}:
      agreed.answer(a, ours)

# whether the World's upload agrees with the hash ez computed
def agreed(+world: PW.World) -> Bool:
  agreed.of(uploaded(world), hash(world))

# why an upload that bend finished does not agree: it printed no line that
# is a name, or a name that is not ours. Both numbers are named, since the
# next question is which walk drifted, and neither is reported as the
# package's name.
def why.read(+ours: String, +text: String) -> String:
  +theirs = other(ours, String.lines(text))
  Bool.pick(String, String.is_empty(theirs),
    "ez: bend printed no line that is a 0x name, so there is nothing to " ++
      "check ez's hash against. bend said:\n" ++ text,
    "ez: ez computed " ++ ours ++ " and bend published " ++ theirs ++
      ". One of the two package walks has drifted from the other, so " ++
      "neither name is safe to write down and ez has reported none.")

# why an upload refuses, `words` being the line it ran. bend has sent the
# package by the time it answers, since it cannot report the hash without
# sending it, so this is said after the fact.
def why.ran(ok: Bool, +words: String, +ours: String, +text: String) -> String:
  match ok:
    case False{}:
      "ez: " ++ words ++ ": " ++ text
    case True{}:
      why.read(ours, text)

def why.answer(got: PW.Answer, +words: String, +ours: String) -> String:
  match got:
    case PW.Ran{ok, text}:
      why.ran(ok, words, ours, text)
    case PW.Told{_t}:
      "ez: bend was not asked to publish"

def why.of(got: PW.Heard, +words: String, +ours: String) -> String:
  match got:
    case PW.Open{}:
      "ez: bend was not asked to publish"
    case PW.Heard{a}:
      why.answer(a, words, ours)

# why the World's upload refuses
def why.upload(+world: PW.World) -> String:
  why.of(uploaded(world),
    String.join(upload.line(entry(world), named.word(named(world))), " "),
    hash(world))

# ---------------------------------------------------------------------------
# the hub packages the package imports

# A package on the hub is built from the hub: whoever imports it has bend
# fetch every hub package it imports in turn. So a package that imports one
# the hub does not have is one no one can build, and `ez publish` asks the
# hub about each before it sends anything, as `cargo publish` refuses a
# dependency that is not on crates.io (EZ-PUB-5). It asks the hub the ledger
# names, the one `ez lock` resolved the imports against.

# a hub package the package imports, as the hub is asked about it: by its
# `0x` name, whose manifest the hub serves at `<hub>/<hash>/manifest`; or by
# its `<name>@<version>`, which the hub resolves at `<hub>/name/<nv>`, with
# the hash ez.lock.toml or ez.toml resolved the name to, "" when neither
# records one
type Probe is Data:
  ProbeHash{hash: String}
  ProbeName{nv: String, hash: String}

# the texts of the package's files
def texts(fs: List<&2, K.Source>) -> List<&2, String>:
  match fs:
    case []:
      []
    case K.Source{_at, text} <> t:
      text <> texts(t)

# a string kept unless it was seen before
def once.pick(dup: Bool, +word: String, rest: List<&2, String>) -> List<&2, String>:
  match dup:
    case True{}:
      rest
    case False{}:
      word <> rest

# each string of a list once, where it first appears
def once.go(xs: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match xs:
    case []:
      []
    case +h <> t:
      once.pick(L.seen.holds(seen, h), h, once.go(t, h <> seen))

# each string of a list once
def once(xs: List<&2, String>) -> List<&2, String>:
  once.go(xs, [])

# the texts of the package the walk made, none while there is none
def sources(+world: PW.World) -> List<&2, String>:
  texts(files.of(walked(world)))

# every `0x` name the package's files import, once each
def hashes(+world: PW.World) -> List<&2, String>:
  once(L.kids(sources(world)))

# every `<name>@<version>` they import, once each
def nvs(+world: PW.World) -> List<&2, String>:
  once(L.kids.named(sources(world)))

# whether a list holds anything
def any(xs: List<&2, String>) -> Bool:
  match xs:
    case []:
      False{}
    case _h <> _t:
      True{}

# the ledger read, a bad one when there is none; the planner reaches this
# stage only past a ledger that parsed
def parsed.of(got: Maybe<&2, String>) -> M.Read:
  match got:
    case None{}:
      M.Bad{"no " ++ PW.toml()}
    case Some{text}:
      M.parse(text)

# the World's ledger, read
def parsed(world: PW.World) -> M.Read:
  parsed.of(PW.ledger(world))

# the hub the ledger names, bend's own when it names none
def hub(world: PW.World) -> String:
  M.hub_of(parsed(world))

# the dependencies the ledger records
def deps.of(got: M.Read) -> List<&2, M.Dep>:
  match got:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _pa, _pv, ds, _ts} = m
      ds

# the dependencies the World's ledger records
def deps(world: PW.World) -> List<&2, M.Dep>:
  deps.of(parsed(world))

# the lock's text, "" when there is none or it was not read
def lock.told(got: TW.Answer) -> String:
  match got:
    case TW.Text{m}:
      F.text_of(m)
    case _:
      ""

def lock.answer(got: PW.Answer) -> String:
  match got:
    case PW.Told{t}:
      lock.told(t)
    case PW.Ran{_ok, _text}:
      ""

def lock.of(got: PW.Heard) -> String:
  match got:
    case PW.Open{}:
      ""
    case PW.Heard{a}:
      lock.answer(a)

# ez.lock.toml as the planner was given it
def lock(+world: PW.World) -> String:
  lock.of(PW.heard(world, PW.Lock{}))

# every name the lock resolves, then every one the ledger records with the
# hash it named when it was added
def names(+world: PW.World) -> List<&2, L.Name>:
  List.append(&2, L.Name, L.names.read(lock(world)), L.ledger.names(parsed(world)))

# each `0x` name as the hub is asked about it
def probes.hash(hs: List<&2, String>) -> List<&2, Probe>:
  match hs:
    case []:
      []
    case h <> t:
      ProbeHash{h} <> probes.hash(t)

# each name, with the hash the lock or the ledger resolves it to
def probes.name(+ns: List<&2, L.Name>, vs: List<&2, String>) -> List<&2, Probe>:
  match vs:
    case []:
      []
    case +h <> t:
      ProbeName{h, L.name.find(ns, h)} <> probes.name(ns, t)

# every hub package the package imports, as the hub is asked about it
def probes(+world: PW.World) -> List<&2, Probe>:
  List.append(&2, Probe, probes.hash(hashes(world)), probes.name(names(world), nvs(world)))

# the url the hub is asked
def probe.url(+hub: String, one: Probe) -> String:
  match one:
    case ProbeHash{h}:
      L.url_of(hub, h, "manifest")
    case ProbeName{nv, _h}:
      hub ++ "/name/" ++ nv

# the question: a GET of that url
def probe.ask(+hub: String, one: Probe) -> PW.Ask:
  PW.Hub{probe.url(hub, one)}

# the questions for a list of them
def probe.asks(+hub: String, ps: List<&2, Probe>) -> List<&2, PW.Ask>:
  match ps:
    case []:
      []
    case h <> t:
      probe.ask(hub, h) <> probe.asks(hub, t)

# the import, as the package's files write it
def probe.word(one: Probe) -> String:
  match one:
    case ProbeHash{h}:
      h
    case ProbeName{nv, _h}:
      nv

# where the ledger says a dependency comes from
def origin.say(src: M.Source) -> String:
  match src:
    case M.Hub{_named}:
      "hub"
    case M.Git{url, _rev, _tag, _root, _nar, _vend}:
      "git " ++ url

# a dependency as a refusal names it: its key and its origin
def dep.say(item: M.Dep) -> String:
  M.Dep{n, _h, _e, src} = item
  n ++ ", " ++ origin.say(src)

# whether the ledger's dependency is the one a probe is about: the same hash,
# or for a name, the same `<name>@<version>` or the hash it resolved to
def dep.is.go(one: Probe, +hash: String, src: M.Source) -> Bool:
  match one:
    case ProbeHash{ph}:
      String.eq(hash, ph)
    case ProbeName{nv, +ph}:
      Bool.or(String.eq(M.source.nv(src), nv),
        Bool.and(Bool.not(String.is_empty(ph)), String.eq(hash, ph)))

def dep.is(one: Probe, item: M.Dep) -> Bool:
  M.Dep{_n, h, _e, src} = item
  dep.is.go(one, h, src)

def dep.find.pick(hit: Bool, item: M.Dep, rest: Unit -> String) -> String:
  match hit:
    case True{}:
      dep.say(item)
    case False{}:
      rest(Unit{})

# the first dependency the ledger records for a probe, said, "" for none
def dep.find(+one: Probe, ds: List<&2, M.Dep>) -> String:
  match ds:
    case []:
      ""
    case +h <> t:
      dep.find.pick(dep.is(one, h), h, _u => dep.find(one, t))

# the import a refusal names, with the dependency key and origin the ledger
# records for it when it records one
def who.of(+word: String, +dep: String) -> String:
  Bool.pick(String, String.is_empty(dep), word, word ++ " (" ++ dep ++ ")")

# a probe as a refusal names it
def who(+one: Probe, ds: List<&2, M.Dep>) -> String:
  who.of(probe.word(one), dep.find(one, ds))

# where one probe stands: on the hub, not asked yet, or off it, with the line
# a refusal says of it
type Seen is Data:
  There{}
  Unasked{}
  Off{line: String}

# what the hub answers for a url it has nothing at: status 404, as
# `Web.get` says it
def absent(+text: String) -> Bool:
  String.eq(text, "the server answered 404")

# the line for a package the hub does not have
def why.absent(+who: String) -> String:
  "  " ++ who ++ " is not on the hub; publish it first"

# the line for one the hub could not be asked about
def why.unasked(+who: String, +text: String) -> String:
  "  " ++ who ++ ": the hub could not be asked: " ++ text

# a GET that did not come back 200: the hub does not have it, or it could not
# be asked. Neither is the hub having it, so both refuse, and nothing is sent
# on a guess.
def seen.miss(gone: Bool, +text: String, +who: String) -> Seen:
  match gone:
    case True{}:
      Off{why.absent(who)}
    case False{}:
      Off{why.unasked(who, text)}

# a manifest the hub served for a `0x` name: the package is there when the
# manifest hashes to the name, as `ez lock` checks it
def seen.hash(ok: Bool, +hash: String, +text: String, +who: String) -> Seen:
  match ok:
    case True{}:
      Bool.pick(Seen, String.starts_with(Sha.hex(text), L.want(hash)), There{},
        Off{"  " ++ who ++ ": the hub served a manifest that does not hash to it"})
    case False{}:
      seen.miss(absent(text), text, who)

# why a name the hub answered is not the package imported
def why.named(+got: String, +want: String, +who: String) -> String:
  Bool.pick(String, String.is_empty(want),
    "  " ++ who ++ ": the hub answered `" ++ got ++ "`, which is not a 0x name",
    "  " ++ who ++ ": the hub names `" ++ got ++ "` by it, and the lock " ++
      "resolved it to " ++ want)

# a name the hub resolved: the package is there when the hub names a `0x`
# name by it, and the one the lock resolved it to when the lock resolved it
def seen.named.go(good: Bool, +got: String, +want: String, +who: String) -> Seen:
  match good:
    case True{}:
      There{}
    case False{}:
      Off{why.named(got, want, who)}

def seen.named(+got: String, +want: String, +who: String) -> Seen:
  seen.named.go(Bool.and(Bool.or(String.eq(got, want), String.is_empty(want)), L.hash.ok(got)),
    got, want, who)

# a name asked of the hub, answered
def seen.name(ok: Bool, +want: String, +text: String, +who: String) -> Seen:
  match ok:
    case True{}:
      seen.named(String.trim(text), want, who)
    case False{}:
      seen.miss(absent(text), text, who)

# a probe's GET answered: whether it came back 200, and what it said
def seen.ran(one: Probe, ok: Bool, +text: String, +who: String) -> Seen:
  match one:
    case ProbeHash{h}:
      seen.hash(ok, h, text, who)
    case ProbeName{_nv, h}:
      seen.name(ok, h, text, who)

def seen.answer(one: Probe, got: PW.Answer, +who: String) -> Seen:
  match got:
    case PW.Ran{ok, text}:
      seen.ran(one, ok, text, who)
    case PW.Told{_t}:
      Off{"  " ++ who ++ ": the hub was not asked"}

def seen.heard(got: PW.Heard, one: Probe, +who: String) -> Seen:
  match got:
    case PW.Open{}:
      Unasked{}
    case PW.Heard{a}:
      seen.answer(one, a, who)

# where a probe stands in a World
def seen(+world: PW.World, +hub: String, +ds: List<&2, M.Dep>, +one: Probe) -> Seen:
  seen.heard(PW.heard(world, probe.ask(hub, one)), one, who(one, ds))

# the probes not asked yet, and the lines for the ones off the hub
type Tally is Data:
  Tally{open: List<&2, Probe>, offs: List<&2, String>}

# a probe still to ask about, added
def tally.unasked(one: Probe, sofar: Tally) -> Tally:
  Tally{open, offs} = sofar
  Tally{one <> open, offs}

# a line for a probe off the hub, added
def tally.offhub(line: String, sofar: Tally) -> Tally:
  Tally{open, offs} = sofar
  Tally{open, line <> offs}

# one probe's standing added to the rest's
def tally.put(standing: Seen, one: Probe, sofar: Tally) -> Tally:
  match standing:
    case There{}:
      sofar
    case Unasked{}:
      tally.unasked(one, sofar)
    case Off{line}:
      tally.offhub(line, sofar)

# every probe'standing standing
def tally(+world: PW.World, +hub: String, +ds: List<&2, M.Dep>, ps: List<&2, Probe>) -> Tally:
  match ps:
    case []:
      Tally{[], []}
    case +h <> t:
      tally.put(seen(world, hub, ds, h), h, tally(world, hub, ds, t))

# every hub package the package imports on the hub, some still to ask about,
# or why the command refuses
type Hubbed is Data:
  OnHub{}
  HubWait{open: List<&2, Probe>}
  OffHub{why: String}

# why a package with imports off the hub is refused: every one of them, and
# the hub that was asked
def why.hub(+hub: String, lines: List<&2, String>) -> String:
  "ez: the package imports hub packages that " ++ hub ++ " does not have, or " ++
    "could not be asked about, and a package on the hub has to build from the " ++
    "hub alone, so nothing was sent:\n" ++ String.join(lines, "\n")

def hubbed.offs(offs: List<&2, String>, +hub: String) -> Hubbed:
  match offs:
    case []:
      OnHub{}
    case h <> t:
      OffHub{why.hub(hub, h <> t)}

# the tally read: every probe asked before any is judged, then every one off
# the hub named at once
def hubbed.go(open: List<&2, Probe>, offs: List<&2, String>, +hub: String) -> Hubbed:
  match open:
    case []:
      hubbed.offs(offs, hub)
    case h <> rest:
      HubWait{h <> rest}

def hubbed.of(sofar: Tally, +hub: String) -> Hubbed:
  Tally{open, offs} = sofar
  hubbed.go(open, offs, hub)

# where the World's hub imports stand
def hubbed(+world: PW.World) -> Hubbed:
  +hub = hub(world)
  hubbed.of(tally(world, hub, deps(world), probes(world)), hub)

# whether they are all on the hub
def on.hub.v(got: Hubbed) -> Bool:
  match got:
    case OnHub{}:
      True{}
    case HubWait{_open}:
      False{}
    case OffHub{_why}:
      False{}

def on.hub(+world: PW.World) -> Bool:
  on.hub.v(hubbed(world))

# ---------------------------------------------------------------------------
# where a World stands

# every check passed, questions still open, or why the command refuses
type Verdict is Data:
  Go{}
  Wait{asks: List<&2, PW.Ask>}
  Stop{why: String}

# what a refusal for a dirty tree says. The lines git printed come with it,
# since the next question is always which file.
def why.dirty(+text: String) -> String:
  "ez: the working tree is dirty, and publishing is public and cannot be " ++
    "taken back, so what goes to the hub has to exist in a commit. git " ++
    "status says:\n" ++ text

# what a refusal for a file git does not track says
def why.stray(+path: String) -> String:
  "ez: " ++ path ++ " is part of the package and git does not track it, " ++
    "so what goes to the hub would not exist in a commit"

# the upload answered: bend's answer agrees, or the command refuses
def decide.agreed(ok: Bool, +world: PW.World) -> Verdict:
  match ok:
    case True{}:
      Go{}
    case False{}:
      Stop{why.upload(world)}

# the upload, asked for once every check before it passed
def decide.upload(got: PW.Heard, +world: PW.World) -> Verdict:
  match got:
    case PW.Open{}:
      Wait{[upload(world)]}
    case PW.Heard{_a}:
      decide.agreed(agreed(world), world)

# the hub imports: every one on the hub goes on to the upload, one still to
# ask about is asked, and any other refuses, sending nothing (EZ-PUB-5)
def decide.hub(on: Hubbed, +world: PW.World) -> Verdict:
  match on:
    case OnHub{}:
      decide.upload(uploaded(world), world)
    case HubWait{open}:
      Wait{probe.asks(hub(world), open)}
    case OffHub{why}:
      Stop{why}

# the lock, read first when the package imports a package by name, since it
# holds the hash the name was resolved to
def decide.lock(need: Bool, got: PW.Heard, +world: PW.World) -> Verdict:
  match need:
    case False{}:
      decide.hub(hubbed(world), world)
    case True{}:
      match got:
        case PW.Open{}:
          Wait{[PW.Lock{}]}
        case PW.Heard{_a}:
          decide.hub(hubbed(world), world)

# every file of the package tracked, or the first that is not refused
def decide.kept(kept: Kept, +world: PW.World) -> Verdict:
  match kept:
    case Kept{}:
      decide.lock(any(nvs(world)), PW.heard(world, PW.Lock{}), world)
    case Stray{path}:
      Stop{why.stray(path)}
    case KeptWait{}:
      Wait{[PW.Tracked{}]}
    case KeptNo{why}:
      Stop{why}

# the walk: a package, a file it asks for, or why there is none
def decide.walk(got: K.Walked, +world: PW.World) -> Verdict:
  match got:
    case K.Walked{_h, _root, _fs, _sums}:
      decide.kept(stray(world), world)
    case K.Asks{at}:
      Wait{[PW.Tool{TW.Read{at}}]}
    case K.Refused{why}:
      Stop{why}

# a status that named a path refuses, and nothing is read or sent
def decide.clean(bad: Bool, +text: String, +world: PW.World) -> Verdict:
  match bad:
    case True{}:
      Stop{why.dirty(text)}
    case False{}:
      decide.walk(walked(world), world)

# git status: asked, answered, or failed
def decide.status(said: Status, +world: PW.World) -> Verdict:
  match said:
    case Said{+text}:
      decide.clean(dirty(text), text, world)
    case StatusWait{}:
      Wait{[locate(world)]}
    case StatusNo{why}:
      Stop{why}

# the ledger: an entry, or why there is none
def decide.led(ledger: Led, +world: PW.World) -> Verdict:
  match ledger:
    case Led{_e, _nv}:
      decide.status(status(world), world)
    case LedNo{why}:
      Stop{why}

# where a World stands
def decide(+world: PW.World) -> Verdict:
  decide.led(led(world), world)

# ---------------------------------------------------------------------------
# the plan

# what the import line names the package by: its `<name>@<version>` when it
# was published under one, its hash otherwise
def called.of(got: Named, +hash: String) -> String:
  match got:
    case ByName{nv}:
      nv
    case ByHash{}:
      hash
    case Unnamed{_why}:
      hash

# what a World's import line names the package by
def called(+world: PW.World) -> String:
  called.of(named(world), hash(world))

# what a publish that agreed says: the hash ez computed, then the import line
# for the entry's path inside the package (`G.import.line`, which `ez add`
# prints too), by the name the package was published under when it has one.
# It writes nothing.
def made(+world: PW.World) -> P.Plan:
  P.Plan{[P.Say{hash(world)}, P.Say{G.import.line(called(world), at(world))}],
    P.Success{}}

# the plan for where a World stands. One that still asks is a World the
# interpreter did not finish, and is refused rather than guessed at.
def plan.v(verdict: Verdict, +world: PW.World) -> P.Plan:
  match verdict:
    case Go{}:
      made(world)
    case Wait{_asks}:
      P.Plan{[], P.Refused{"ez: the publish of " ++ entry(world) ++
        " was never resolved"}}
    case Stop{why}:
      P.Plan{[], P.Refused{why}}

# `ez publish` over a World
def plan(+world: PW.World) -> P.Plan:
  plan.v(decide(world), world)

# the questions still open, or the plan once there are none
type Step is Data:
  Asking{asks: List<&2, PW.Ask>}
  Run{plan: P.Plan}

# the step for where the World stands
def step.v(verdict: Verdict, +world: PW.World) -> Step:
  match verdict:
    case Go{}:
      Run{made(world)}
    case Wait{asks}:
      Asking{asks}
    case Stop{why}:
      Run{plan.v(Stop{why}, world)}

# what the interpreter does next on a World
def step(+world: PW.World) -> Step:
  step.v(decide(world), world)

# ---------------------------------------------------------------------------
# law vocabulary

# whether a plan ends in success
def succeeds.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      True{}
    case P.Refused{_why}:
      False{}

# whether `ez publish` succeeds on a World
def succeeds(+world: PW.World) -> Bool:
  succeeds.plan(plan(world))

# whether `ez publish` refuses on a World
def refuses(+world: PW.World) -> Bool:
  Bool.not(succeeds(world))

# whether a verdict refuses outright: it asks nothing and sends nothing
def stops.v(verdict: Verdict) -> Bool:
  match verdict:
    case Go{}:
      False{}
    case Wait{_asks}:
      False{}
    case Stop{_why}:
      True{}

# whether `ez publish` refuses a World outright, asking nothing more
def stops(+world: PW.World) -> Bool:
  stops.v(decide(world))

# whether a question is the upload
def is.upload(ask: PW.Ask) -> Bool:
  match ask:
    case PW.Upload{_entry, _named, _says}:
      True{}
    case PW.Tool{_q}:
      False{}
    case PW.Tracked{}:
      False{}
    case PW.Lock{}:
      False{}
    case PW.Hub{_url}:
      False{}

# whether any of these questions is the upload
def any.upload(asks: List<&2, PW.Ask>) -> Bool:
  match asks:
    case []:
      False{}
    case h <> t:
      +rest = any.upload(t)
      Bool.or(is.upload(h), rest)

# whether a verdict is at the upload or past it: it asks for the upload, or
# has its answer and goes on
def sends.v(verdict: Verdict) -> Bool:
  match verdict:
    case Go{}:
      True{}
    case Wait{asks}:
      any.upload(asks)
    case Stop{_why}:
      False{}

# whether `ez publish` gets as far as the upload on a World
def sends(+world: PW.World) -> Bool:
  sends.v(decide(world))
