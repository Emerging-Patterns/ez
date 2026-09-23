# lock/world: a spike of `ez lock` in planner form, for the design in
# docs/rfc/ez-lock-planner.md. Nothing imports this module: `ez lock` still
# runs lock/lock.bend, and this file changes none of its behavior. It exists
# to show that the World and the planner the design proposes are total pure
# Bend terms the checker accepts, and that a quantified law over the World
# can be proved about them.
#
# The planner here is plain `ez lock` without `--upgrade`. It reads a World,
# which is everything the interpreter gathered, and returns an Outcome: the
# lock's text, a refusal, or the packages it still needs answers for. The
# interpreter this design pairs it with asks for those, adds the answers to
# the World, and runs the planner again, until the outcome is not a request.
import Base
import ../lock.bend as L
import ../../manifest/manifest.bend as M
import ../../pkg/pkg.bend as K
import ../../hub/hub.bend as Web
import ../../sha/sha.bend as Sha
import ../../ez/pin.bend as Pin

# how the interpreter came by a package's bytes. A tree already under
# BEND_LIB, vendored or left by an earlier lock, was read from there. One that
# was not was cloned at the rev the ledger pins, and weighed. A hub package was
# served by the hub.
type How is Data:
  Lib{}
  Clone{nar: String}
  Served{}

# the interpreter's answer for one package: the manifest it found and the text
# of each file the manifest names, in the manifest's order, or why there was
# none
type Answer is Data:
  Got{how: How, manifest: String, srcs: List<&2, String>}
  Miss{why: String}

# one package hash, answered
type Reply is Data:
  Reply{hash: String, answer: Answer}

# one committed `.bend` file: its path and its text
type Source is Data:
  Source{at: String, text: String}

# what `git ls-files '*.bend'` answered: the committed sources, or why git
# could not list them
type Listing is Data:
  Listed{files: List<&2, Source>}
  Unlisted{why: String}

# everything plain `ez lock` reads. The ledger's text, the committed sources,
# and one reply per package hash the planner has asked about so far. There is
# no field for the environment, the clock, the old lock, untracked files or
# `.ez/origins.toml`, because the lock reads none of them.
type World is Data:
  World{ledger: String, listing: Listing, replies: List<&2, Reply>}

# what the planner makes of one answer: the files and their texts, once every
# check passed, or why it refused them
type Verdict is Data:
  Ok{files: List<&2, K.File>, srcs: List<&2, String>}
  No{why: String}

# one package hash and its verdict
type Judged is Data:
  Judged{hash: String, verdict: Verdict}

# the part of a World the lock may depend on. A reply enters only through its
# verdict, so how the bytes arrived does not, and bytes that failed a check
# enter only as the refusal they caused.
type Inputs is Data:
  Inputs{ledger: String, listing: Listing, judged: List<&2, Judged>}

# what plain `ez lock` does: write this text to ez.lock.toml and exit 0, refuse
# with exit 1, or ask the interpreter for these packages first
type Outcome is Data:
  Locked{text: String}
  Refused{why: String}
  Asking{hashes: List<&2, String>}

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

# the verdict once the texts were weighed against the manifest
def body.sums(ok: Bool, +hash: String, fs: List<&2, K.File>, ss: List<&2, String>) -> Verdict:
  match ok:
    case True{}:
      Ok{fs, ss}
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
# package, and each text hashes to its file's sum. The first check is new: a
# tree under BEND_LIB was trusted to be the tree its directory named.
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

# one answer judged
def accept(+orgs: List<&2, L.Origin>, +hash: String, answer: Answer) -> Verdict:
  match answer:
    case Miss{why}:
      No{why}
    case Got{how, manifest, ss}:
      accept.src(L.origin(orgs, hash), how, hash, manifest, ss)

# every reply judged, in the order they were given
def judge(+orgs: List<&2, L.Origin>, rs: List<&2, Reply>) -> List<&2, Judged>:
  match rs:
    case []:
      []
    case Reply{+hash, answer} <> t:
      Judged{hash, accept(orgs, hash, answer)} <> judge(orgs, t)

# the origins a ledger's text records
def origins(+ledger: String) -> List<&2, L.Origin>:
  L.ledger.read(M.parse(ledger))

# what a World is, as far as the lock may tell
def inputs(world: World) -> Inputs:
  World{+ledger, listing, replies} = world
  Inputs{ledger, listing, judge(origins(ledger), replies)}

# ---------------------------------------------------------------------------
# the walk

# a verdict looked up, or none when nothing has been asked about the hash yet
type Look is Data:
  Found{verdict: Verdict}
  Absent{}

# this verdict when it is the hash asked for, otherwise the rest's
def look.at(hit: Bool, verdict: Verdict, rest: Look) -> Look:
  match hit:
    case True{}:
      Found{verdict}
    case False{}:
      rest

# the first verdict recorded for a hash
def look(js: List<&2, Judged>, +hash: String) -> Look:
  match js:
    case []:
      Absent{}
    case Judged{+h, v} <> t:
      look.at(String.eq(h, hash), v, look(t, hash))

# a walk in progress: the hashes still queued, the packages resolved, the
# hashes still to be asked about, and the first refusal, "" while there is
# none. The walk is one step, which does not recurse, iterated; so a fact
# about the walk is a fact about one step, carried by induction on the fuel.
type Walk is Data:
  Walk{queue: List<&2, String>, packs: List<&2, L.Pack>, asks: List<&2, String>, bad: String}

# the first refusal wins
def first(+bad: String, why: String) -> String:
  Bool.pick(String, String.is_empty(bad), why, bad)

# one package, by its verdict
def step.verdict(
  verdict: Verdict,
  +src: L.Src,
  +hash: String,
  rest: List<&2, String>,
  packs: List<&2, L.Pack>,
  asks: List<&2, String>,
  bad: String
) -> Walk:
  match verdict:
    case No{why}:
      Walk{rest, packs, asks, first(bad, why)}
    case Ok{fs, ss}:
      Walk{List.append(&2, String, rest, L.kids(ss)), L.Pack{hash, src, fs} <> packs,
        asks, bad}

# one package, asked about when nothing has answered for it yet
def step.look(
  found: Look,
  +src: L.Src,
  +hash: String,
  rest: List<&2, String>,
  packs: List<&2, L.Pack>,
  asks: List<&2, String>,
  bad: String
) -> Walk:
  match found:
    case Absent{}:
      Walk{rest, packs, hash <> asks, bad}
    case Found{v}:
      step.verdict(v, src, hash, rest, packs, asks, bad)

# a hash already resolved, or already asked about, is passed over
def step.pick(
  seen: Bool,
  +orgs: List<&2, L.Origin>,
  +js: List<&2, Judged>,
  +hash: String,
  rest: List<&2, String>,
  packs: List<&2, L.Pack>,
  asks: List<&2, String>,
  bad: String
) -> Walk:
  match seen:
    case True{}:
      Walk{rest, packs, asks, bad}
    case False{}:
      step.look(look(js, hash), L.origin(orgs, hash), hash, rest, packs, asks, bad)

# the next hash of the queue, or the walk as it is when the queue is empty
def step.pop(
  +orgs: List<&2, L.Origin>,
  +js: List<&2, Judged>,
  queue: List<&2, String>,
  +packs: List<&2, L.Pack>,
  +asks: List<&2, String>,
  bad: String
) -> Walk:
  match queue:
    case []:
      Walk{[], packs, asks, bad}
    case +h <> t:
      step.pick(Bool.or(L.has(packs, h), L.seen.holds(asks, h)), orgs, js, h, t,
        packs, asks, bad)

# one step of the walk
def step(+orgs: List<&2, L.Origin>, +js: List<&2, Judged>, wk: Walk) -> Walk:
  Walk{queue, packs, asks, bad} = wk
  step.pop(orgs, js, queue, packs, asks, bad)

# whether a walk has nothing left in its queue
def walk.done(+wk: Walk) -> Bool:
  Walk{queue, _packs, _asks, _bad} = wk
  List.is_empty(&2, String, queue)

# a walk that ran out of fuel with its queue not empty, refused
def walk.spent(wk: Walk) -> Walk:
  Walk{queue, packs, asks, bad} = wk
  Walk{queue, packs, asks, first(bad, "ez: the import graph is too deep to lock")}

# the walk as it is when it is done, or one step further when it is not. The
# rest of the walk arrives as a function, since a def may not call itself from
# another def.
def walk.more(done: Bool, wk: Walk, go: Walk -> Walk) -> Walk:
  match done:
    case True{}:
      wk
    case False{}:
      go(wk)

# the fuel ran out: refused, unless the walk had just finished
def walk.out(done: Bool, wk: Walk) -> Walk:
  match done:
    case True{}:
      wk
    case False{}:
      walk.spent(wk)

# every package the queue reaches, each one once. A walk that runs out of fuel
# with the queue not empty is a refusal, never a lock of what it had so far.
def walk(fuel: Nat, +orgs: List<&2, L.Origin>, +js: List<&2, Judged>, +wk: Walk) -> Walk:
  match fuel:
    case 0n:
      walk.out(walk.done(wk), wk)
    case 1n+f:
      walk.more(walk.done(wk), wk, now => walk(f, orgs, js, step(orgs, js, now)))

# ---------------------------------------------------------------------------
# the plan

# every hub package one committed source imports
def roots.one(+src: Source) -> List<&2, String>:
  Source{at, text} = src
  Bool.pick(List<&2, String>, String.starts_with(at, ".ez/"), [],
    L.specs(K.scan.mods(K.scan(text))))

# every hub package the committed sources import. Every committed `.bend`
# file is a root, so no local import has to be followed, and a file that is
# not committed is never read.
def roots(fs: List<&2, Source>) -> List<&2, String>:
  match fs:
    case []:
      []
    case +h <> t:
      List.append(&2, String, roots.one(h), roots(t))

# a walk with questions left is a request; one without is the lock
def outcome.asks(asks: List<&2, String>, +hub: String, packs: List<&2, L.Pack>, ts: List<&2, M.Tool>) -> Outcome:
  match asks:
    case []:
      Locked{L.render.tools(ts, hub, packs)}
    case h <> t:
      Asking{h <> t}

# a refusal wins over a request, so a package that failed its checks stops
# the lock before anything else is fetched
def outcome.bad(
  clean: Bool,
  +bad: String,
  asks: List<&2, String>,
  +hub: String,
  packs: List<&2, L.Pack>,
  ts: List<&2, M.Tool>
) -> Outcome:
  match clean:
    case True{}:
      outcome.asks(asks, hub, packs, ts)
    case False{}:
      Refused{bad}

# the walk's result as an outcome: a refusal, a request, or the lock
def outcome(wk: Walk, +hub: String, ts: List<&2, M.Tool>) -> Outcome:
  Walk{_queue, packs, asks, +bad} = wk
  outcome.bad(String.is_empty(bad), bad, asks, hub, packs, ts)

# the lock of a listing, once the tool pins were found complete
def plan.listed.go(complete: Bool, +why: String, +led: M.Read, fs: List<&2, Source>, +js: List<&2, Judged>) -> Outcome:
  match complete:
    case True{}:
      outcome(walk(U32.to_nat(100000), L.ledger.read(led), js,
        Walk{roots(fs), [], [], ""}), M.hub_of(led), M.tools_of(led))
    case False{}:
      Refused{why}

def plan.listed(+why: String, +led: M.Read, fs: List<&2, Source>, +js: List<&2, Judged>) -> Outcome:
  plan.listed.go(String.is_empty(why), why, led, fs, js)

# why a plain lock cannot copy the ledger's tool pins, or "" when it can. A
# ledger that does not parse is refused here too.
def need.why(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{why}:
      "ez: " ++ why
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _ds, ts} = m
      Pin.gaps(ts)

# the lock of a ledger that parsed, or its refusal
def plan.led(+led: M.Read, listing: Listing, +js: List<&2, Judged>) -> Outcome:
  match listing:
    case Unlisted{why}:
      Refused{why}
    case Listed{fs}:
      plan.listed(need.why(led), led, fs, js)

# plain `ez lock` over what the lock may depend on
def plan.of(ins: Inputs) -> Outcome:
  Inputs{ledger, listing, js} = ins
  plan.led(M.parse(ledger), listing, js)

# plain `ez lock` over a World
def plan(world: World) -> Outcome:
  plan.of(inputs(world))

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

# every answer as a fresh clone would have it
def reclone(+orgs: List<&2, L.Origin>, rs: List<&2, Reply>) -> List<&2, Reply>:
  match rs:
    case []:
      []
    case Reply{+hash, answer} <> t:
      Reply{hash, reclone.one(orgs, hash, answer)} <> reclone(orgs, t)
