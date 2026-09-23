# lock/world: everything `ez lock` reads, as one value, and what the lock may
# depend on in it. The planner (lock/plan.bend) is a pure function of a
# World; the interpreter (lock/run.bend) gathers one, answering each question
# the planner asks by IO, and executes the plan the planner returns. The
# design is docs/rfc/ez-lock-planner.md.
#
# A World is the ledger's text, the committed `.bend` files, one answer per
# package the planner asked about, and, under `--upgrade`, one answer per
# question the upgrade asked (lock/up.bend). There is no field for the
# environment, the clock, the old lock, untracked files, `.ez/origins.toml` or
# BEND_LIB's path, because the lock reads none of them.
import Base
import ./lock.bend as L
import ./up.bend as Up
import ../manifest/upgrade.bend as U
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../hub/hub.bend as Web
import ../sha/sha.bend as Sha
import ../ez/say.bend as Say

# the command as it was run: `--upgrade`, the name `--package` gave ("" for
# none), and the directory it runs in, which is the project root. A relative
# path source is recorded as it was given, relative to that root, and every
# question the lock asks about it names it anchored there, as the planner
# computes it (`P.anchor.src`, `Up.anchor`).
type Args is Data:
  Args{upgrade: Bool, only: String, here: String}

# one committed `.bend` file: its path and its text
type Source is Data:
  Source{at: String, text: String}

# what `git ls-files '*.bend'` answered: the committed sources, or why git
# could not list them
type Listing is Data:
  Listed{files: List<&2, Source>}
  Unlisted{why: String}

# how the interpreter came by a package's bytes. A tree already under
# BEND_LIB, vendored or left by an earlier lock, was read from there. One that
# was not was cloned at the rev the ledger pins, and weighed. A hub package was
# served by the hub.
type How is Data:
  Lib{}
  Clone{nar: String}
  Served{}

# a question the planner asks, answered by one IO action: a package's
# manifest and the text of each file it names. The source says where to read
# it from, and the hub is where a hub package is served.
type Ask is Data:
  Pkg{hash: String, src: L.Src, hub: String}

# the answer to one question: the manifest found and the text of each file it
# names, in the manifest's order, or why IO could not answer
type Answer is Data:
  Got{how: How, manifest: String, srcs: List<&2, String>}
  Miss{why: String}

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `ez lock` reads. The ledger is ez.toml's text, or None when
# there is no ez.toml. `ups` answers the upgrade's questions, and is empty for
# a plain lock, which asks none.
type World is Data:
  World{args: Args, ledger: Maybe<&2, String>, listing: Listing,
    replies: List<&2, Reply>, ups: List<&2, Up.Reply>}

# what the planner makes of one answer: the files and their texts, once every
# check passed, or why it refused them
type Verdict is Data:
  Ok{files: List<&2, K.File>, srcs: List<&2, String>}
  No{why: String}

# one package hash and its verdict
type Judged is Data:
  Judged{hash: String, verdict: Verdict}

# the part of a World the lock may depend on: the ledger the lock is made
# from, read, which under `--upgrade` is the one the upgrade leaves; why the
# upgrade refuses, "" when it does not; the committed sources; and the verdict
# on every package. A reply enters only through its verdict, so how the bytes
# arrived does not, and bytes that failed a check enter only as the refusal
# they caused.
type Inputs is Data:
  Inputs{ledger: M.Read, stop: String, listing: Listing, judged: List<&2, Judged>}

# whether the command was `ez lock --upgrade`
def args.upgrade(world: World) -> Bool:
  World{args, _ledger, _listing, _replies, _ups} = world
  Args{up, _only, _here} = args
  up

# the name `--package` gave, "" for none
def args.only(world: World) -> String:
  World{args, _ledger, _listing, _replies, _ups} = world
  Args{_up, only, _here} = args
  only

# the directory the command runs in
def here.of(args: Args) -> String:
  Args{_up, _only, here} = args
  here

# the directory the lock runs in, which is the project root
def args.here(world: World) -> String:
  World{args, _ledger, _listing, _replies, _ups} = world
  here.of(args)

# the ledger's text
def ledger.of(world: World) -> Maybe<&2, String>:
  World{_args, ledger, _listing, _replies, _ups} = world
  ledger

# the hash a question asks about
def ask.hash(ask: Ask) -> String:
  Pkg{hash, _src, _hub} = ask
  hash

# ---------------------------------------------------------------------------
# judging one answer

# whether every text hashes to the sum its file is recorded with. A list of
# texts that is longer or shorter than the files is not the package.
def sums.ok(fs: List<&2, K.File>, ss: List<&2, String>) -> Bool:
  match fs ss:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{_h, _t}:
      False{}
    case Con{_f, _g} Nil{}:
      False{}
    case Con{f, g} Con{s, t}:
      +rest = sums.ok(g, t)
      Bool.and(String.eq(Sha.hex(s), K.file.sum(f)), rest)

# each file with its text, as it is laid
def laid(fs: List<&2, K.File>, ss: List<&2, String>) -> List<&2, Source>:
  match fs ss:
    case Nil{} Nil{}:
      []
    case Nil{} Con{_s, _t}:
      []
    case Con{_f, _g} Nil{}:
      []
    case Con{f, g} Con{s, t}:
      Source{K.file.at(f), s} <> laid(g, t)

# a laid file weighed by its own text
def weigh(src: Source) -> K.File:
  Source{at, +text} = src
  K.File{at, Sha.hex(text)}

# every laid file weighed by its own text
def weighs(ls: List<&2, Source>) -> List<&2, K.File>:
  match ls:
    case []:
      []
    case h <> t:
      weigh(h) <> weighs(t)

# the manifest of the files laid, weighed by their own texts, which is the
# manifest a tree is laid with
def manifest(+ls: List<&2, Source>) -> String:
  K.manifest_of(K.files_of(weighs(ls)))

# the `0x` name of that manifest
def named(+ls: List<&2, Source>) -> String:
  K.hash_of(K.files_of(weighs(ls)))

# the verdict once the files, weighed by their own texts, were asked whether
# they hash to the name. Their manifest is the one the tree is laid with, and
# the manifest that was read hashes to the name already, so a package whose
# manifest is not written the way ez writes one (a line per file, in path
# order, each file once) is refused here rather than laid under a name its
# laid manifest does not hash to.
def body.laid(ok: Bool, +hash: String, fs: List<&2, K.File>, ss: List<&2, String>) -> Verdict:
  match ok:
    case True{}:
      Ok{fs, ss}
    case False{}:
      No{"ez: " ++ hash ++ ": its manifest is not written the way its name is taken" ++
        " (one line per file, in path order, each file once)"}

# the verdict once the texts were weighed against the manifest
def body.sums(ok: Bool, +hash: String, +fs: List<&2, K.File>, +ss: List<&2, String>) -> Verdict:
  match ok:
    case True{}:
      body.laid(String.eq(hash, named(laid(fs, ss))), hash, fs, ss)
    case False{}:
      No{"ez: " ++ hash ++ ": a file does not match its manifest"}

# the verdict once each path was asked whether it escapes the package
def body.escape.go(clean: Bool, +bad: String, +hash: String, +fs: List<&2, K.File>, +ss: List<&2, String>) -> Verdict:
  match clean:
    case True{}:
      body.sums(sums.ok(fs, ss), hash, fs, ss)
    case False{}:
      No{"ez: " ++ hash ++ ": its manifest escapes the package (" ++ bad ++ ")"}

# the verdict once no path was found to escape the package
def body.escape(+bad: String, +hash: String, +fs: List<&2, K.File>, +ss: List<&2, String>) -> Verdict:
  body.escape.go(String.is_empty(bad), bad, hash, fs, ss)

# the verdict once the manifest was known to be the one the hash names
def body.named(ok: Bool, +hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  match ok:
    case True{}:
      +fs = L.manifest.files(String.lines(manifest))
      body.escape(K.escaped(fs), hash, fs, ss)
    case False{}:
      No{"ez: " ++ hash ++ ": its manifest does not hash to its name"}

# a package's bytes, checked the same way whatever they came from: the
# manifest is the one the `0x` name is the digest of, no path leaves the
# package, each text hashes to its file's sum, and the files, weighed by their
# own texts, hash to the name, which is `ez fetch`'s check too. A tree under
# BEND_LIB is checked against its name like any other, so a stale or edited
# tree there is refused rather than locked.
def body(+hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  body.named(Web.matches(L.want(hash), manifest), hash, manifest, ss)

# a git package that arrived with no files is refused, never locked as an
# empty table
def git.body(empty: Bool, +hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  match empty:
    case True{}:
      No{"ez: " ++ hash ++ ": its manifest names no files"}
    case False{}:
      body(hash, manifest, ss)

# a git package's bytes once its checkout was weighed. A tree read from
# BEND_LIB is judged as a clone that weighed to the narHash the ledger
# records, so the same bytes lock the same way whichever way they came.
def git.weighed.go(same: Bool, +why: String, +hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  match same:
    case True{}:
      git.body(List.is_empty(&2, K.File, L.manifest.files(String.lines(manifest))),
        hash, manifest, ss)
    case False{}:
      No{why}

def git.weighed(+why: String, +hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  git.weighed.go(String.is_empty(why), why, hash, manifest, ss)

# a git package, by how it arrived
def git.how(
  how: How,
  +hash: String,
  +url: String,
  +rev: String,
  +nar: String,
  +manifest: String,
  +ss: List<&2, String>
) -> Verdict:
  match how:
    case Lib{}:
      git.weighed(L.nar.why(nar, nar, url, rev), hash, manifest, ss)
    case Clone{got}:
      git.weighed(L.nar.why(nar, got, url, rev), hash, manifest, ss)
    case Served{}:
      No{"ez: " ++ hash ++ " is a git package and was not read from git"}

# a hub package, by how it arrived. Only the hub serves one.
def hub.how(how: How, +hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  match how:
    case Lib{}:
      No{"ez: " ++ hash ++ " is a hub package and was not served by the hub"}
    case Clone{_got}:
      No{"ez: " ++ hash ++ " is a hub package and was not served by the hub"}
    case Served{}:
      body(hash, manifest, ss)

# a package's answer against where the ledger says it comes from
def accept.src(src: L.Src, how: How, +hash: String, +manifest: String, +ss: List<&2, String>) -> Verdict:
  match src:
    case L.Hub{}:
      hub.how(how, hash, manifest, ss)
    case L.Git{url, rev, _entry, _root, nar, _tag}:
      git.how(how, hash, url, rev, nar, manifest, ss)

# why a hub package could not be read. One the ledger names is explained the
# way a hub miss always was. One it does not name is said to be unnamed, since
# that, and not the hub, is what a person has to fix.
def hub.why(named: Bool, +hash: String, +hub: String, +why: String) -> String:
  match named:
    case True{}:
      Say.hub.explain(hash, L.url_of(hub, hash, "manifest"), why)
    case False{}:
      "ez: " ++ hash ++ " is imported, ez.toml does not name it, and the hub at " ++
        hub ++ " did not serve it (" ++ why ++ "). A package taken from git is recorded with `ez add`."

# why IO could not answer, said for where the package comes from
def miss.src(src: L.Src, named: Bool, +hash: String, +hub: String, +why: String) -> String:
  match src:
    case L.Hub{}:
      hub.why(named, hash, hub, why)
    case L.Git{_url, _rev, _entry, _root, _nar, _tag}:
      why

# one answer judged
def accept(+orgs: List<&2, L.Origin>, +hub: String, +hash: String, answer: Answer) -> Verdict:
  match answer:
    case Miss{why}:
      No{miss.src(L.origin(orgs, hash), L.known(orgs, hash), hash, hub, why)}
    case Got{how, manifest, ss}:
      accept.src(L.origin(orgs, hash), how, hash, manifest, ss)

# every reply judged, in the order they were given
def judge(+orgs: List<&2, L.Origin>, +hub: String, rs: List<&2, Reply>) -> List<&2, Judged>:
  match rs:
    case []:
      []
    case Reply{ask, answer} <> t:
      +hash = ask.hash(ask)
      Judged{hash, accept(orgs, hub, hash, answer)} <> judge(orgs, hub, t)

# the ledger, read. A missing one is refused as a ledger that does not
# parse: only `ez init` makes a ledger, and a lock of none is not a lock.
def parsed(ledger: Maybe<&2, String>) -> M.Read:
  match ledger:
    case None{}:
      M.Bad{"no ez.toml here; ez lock works on a project's ledger, and ez init makes one"}
    case Some{text}:
      M.parse(text)

# the origins a ledger records
def origins(+ledger: Maybe<&2, String>) -> List<&2, L.Origin>:
  L.ledger.read(parsed(ledger))

# the dependency ez.toml names `name`, as `M.dep` finds it
def dep(world: World, name: String) -> M.Dep:
  World{_args, ledger, _listing, _replies, _ups} = world
  M.dep(parsed(ledger), name)

# the hub a ledger names
def ledger.hub(+ledger: Maybe<&2, String>) -> String:
  M.hub_of(parsed(ledger))

# ---------------------------------------------------------------------------
# the ledger the lock is made from

# a plain lock's is ez.toml as it is. An upgrade's is what the upgrade
# decides on its answers: the ledger it writes, or its refusal, or the
# questions it still has.
def next.up(up: Bool, +only: String, +ledger: Maybe<&2, String>, ups: List<&2, Up.Reply>) -> Up.Next:
  match up:
    case False{}:
      Up.plain(parsed(ledger))
    case True{}:
      Up.next(only, parsed(ledger), ups)

# what the upgrade decides on a World, or nothing around a plain lock
def next(args: Args, +ledger: Maybe<&2, String>, ups: List<&2, Up.Reply>) -> Up.Next:
  Args{up, +only, _here} = args
  next.up(up, only, ledger, ups)

# the origins the lock reads packages by
def next.origins(+nx: Up.Next) -> List<&2, L.Origin>:
  L.ledger.read(Up.next.read(nx))

# the hub it names
def next.hub(+nx: Up.Next) -> String:
  M.hub_of(Up.next.read(nx))

# a tree the upgrade checked out at a new rev, as the answer to the package
# question the lock would ask about it: a clone, weighed
def laid.reply(laid: Up.Laid, +orgs: List<&2, L.Origin>, +hub: String) -> Reply:
  Up.Laid{+hash, nar, manifest, srcs} = laid
  Reply{Pkg{hash, L.origin(orgs, hash), hub}, Got{Clone{nar}, manifest, srcs}}

def laid.replies(ls: List<&2, Up.Laid>, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, Reply>:
  match ls:
    case []:
      []
    case h <> t:
      laid.reply(h, orgs, hub) <> laid.replies(t, orgs, hub)

# the package answers the lock reads: the trees the upgrade checked out, then
# every answer the World holds
def replies.of(+nx: Up.Next, replies: List<&2, Reply>) -> List<&2, Reply>:
  List.append(&2, Reply,
    laid.replies(Up.next.trees(nx), next.origins(nx), next.hub(nx)), replies)

# every package answer judged against the ledger the lock is made from
def judged.of(+nx: Up.Next, replies: List<&2, Reply>) -> List<&2, Judged>:
  List.append(&2, Judged,
    judge(next.origins(nx), next.hub(nx),
      laid.replies(Up.next.trees(nx), next.origins(nx), next.hub(nx))),
    judge(next.origins(nx), next.hub(nx), replies))

# every committed source with each hash the upgrade moved rewritten in its
# imports, as the upgrade writes it
def sources.swap(+ss: List<&2, U.Swap>, fs: List<&2, Source>) -> List<&2, Source>:
  match fs:
    case []:
      []
    case Source{at, text} <> t:
      Source{at, U.reimport.many(ss, text)} <> sources.swap(ss, t)

def listing.swap(+ss: List<&2, U.Swap>, listing: Listing) -> Listing:
  match listing:
    case Listed{fs}:
      Listed{sources.swap(ss, fs)}
    case Unlisted{why}:
      Unlisted{why}

# the committed sources as the lock reads them: as the upgrade leaves them,
# which is as they are when no hash moved, and always for a plain lock
def listing.moved(ss: List<&2, U.Swap>, listing: Listing) -> Listing:
  match ss:
    case []:
      listing
    case h <> t:
      listing.swap(h <> t, listing)

def listing.of(+nx: Up.Next, listing: Listing) -> Listing:
  listing.moved(Up.next.swaps(nx), listing)

# what a World is, as far as the lock may tell, once the upgrade decided
def inputs.of(+nx: Up.Next, listing: Listing, replies: List<&2, Reply>) -> Inputs:
  Inputs{Up.next.read(nx), Up.next.stop(nx), listing.of(nx, listing),
    judged.of(nx, replies)}

# what a World is, as far as the lock may tell
def inputs(world: World) -> Inputs:
  World{args, +ledger, listing, replies, ups} = world
  inputs.of(next(args, ledger, ups), listing, replies)

# ---------------------------------------------------------------------------
# a fresh clone's World

# one answer as a fresh clone would have it: a tree read from BEND_LIB is
# instead cloned at the rev the ledger pins and weighed to the narHash the
# ledger records. Anything else is what it was.
def reclone.how(how: How, +src: L.Src) -> How:
  match how:
    case Lib{}:
      Clone{L.src.nar(src)}
    case Clone{got}:
      Clone{got}
    case Served{}:
      Served{}

def reclone.one(+orgs: List<&2, L.Origin>, +hash: String, answer: Answer) -> Answer:
  match answer:
    case Miss{why}:
      Miss{why}
    case Got{how, manifest, ss}:
      Got{reclone.how(how, L.origin(orgs, hash)), manifest, ss}

# every answer as a fresh clone would have it. A tree the upgrade checked
# out is a clone already.
def reclone.all(+orgs: List<&2, L.Origin>, rs: List<&2, Reply>) -> List<&2, Reply>:
  match rs:
    case []:
      []
    case Reply{+ask, answer} <> t:
      Reply{ask, reclone.one(orgs, ask.hash(ask), answer)} <> reclone.all(orgs, t)

# the World a fresh clone of the same commit gathers: the same ledger, the
# same committed sources, and every tree it would have read from BEND_LIB
# cloned and weighed instead, since a clone has nothing there
def reclone(world: World) -> World:
  World{+args, +ledger, listing, replies, +ups} = world
  World{args, ledger, listing,
    reclone.all(next.origins(next(args, ledger, ups)), replies), ups}
