# lock/plan: plain `ez lock` as a pure planner. It reads a World
# (lock/world.bend) and returns either the packages it still needs answered
# (`wants`) or a Plan: the effects to run and how the command ends (`plan`).
# The interpreter (lock/run.bend) loops on `wants`, answering each question by
# IO, until nothing is left to ask, then runs `plan` once and executes it.
#
# `wants` only scans the answers it has for imports; `plan` checks every
# package once, so a lock pays for each file's SHA-256 once however deep the
# import graph is. A package that fails a check may make `wants` ask for more
# than the lock needs, which costs a fetch and changes nothing, since `plan`
# refuses it.
#
# What a plain lock decides depends on a World only through `W.inputs`: the
# ledger, the committed sources, and the verdict on every answer. How a tree
# arrived only decides whether it is laid under BEND_LIB for the build that
# follows, which is a cache and not something the lock records.
import Base
import ./world.bend as W
import ./lock.bend as L
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../ez/pin.bend as Pin

# ---------------------------------------------------------------------------
# the walk

# a verdict looked up, or none when nothing has been asked about the hash yet
type Look is Data:
  Found{verdict: W.Verdict}
  Absent{}

# this verdict when it is the hash asked for, otherwise the rest's
def look.at(hit: Bool, verdict: W.Verdict, rest: Look) -> Look:
  match hit:
    case True{}:
      Found{verdict}
    case False{}:
      rest

# the first verdict recorded for a hash
def look(js: List<&2, W.Judged>, +hash: String) -> Look:
  match js:
    case []:
      Absent{}
    case W.Judged{+h, v} <> t:
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
  verdict: W.Verdict,
  +src: L.Src,
  +hash: String,
  rest: List<&2, String>,
  packs: List<&2, L.Pack>,
  asks: List<&2, String>,
  bad: String
) -> Walk:
  match verdict:
    case W.No{why}:
      Walk{rest, packs, asks, first(bad, why)}
    case W.Ok{fs, ss}:
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
  +js: List<&2, W.Judged>,
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
  +js: List<&2, W.Judged>,
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
def walk.step(+orgs: List<&2, L.Origin>, +js: List<&2, W.Judged>, wk: Walk) -> Walk:
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
def walk(fuel: Nat, +orgs: List<&2, L.Origin>, +js: List<&2, W.Judged>, +wk: Walk) -> Walk:
  match fuel:
    case 0n:
      walk.out(walk.done(wk), wk)
    case 1n+f:
      walk.more(walk.done(wk), wk, now => walk(f, orgs, js, walk.step(orgs, js, now)))

# the packages a walk has resolved
def walk.packs(wk: Walk) -> List<&2, L.Pack>:
  Walk{_queue, packs, _asks, _bad} = wk
  packs

# every hub package one committed source imports. The committed trees under
# `.ez/` are packages, not the project's own sources.
def roots.one(+src: W.Source) -> List<&2, String>:
  W.Source{at, text} = src
  Bool.pick(List<&2, String>, String.starts_with(at, ".ez/"), [],
    L.specs(K.scan.mods(K.scan(text))))

# every hub package the committed sources import. Every committed `.bend`
# file is a root, so no local import has to be followed, and a file that is
# not committed is never read.
def roots(fs: List<&2, W.Source>) -> List<&2, String>:
  match fs:
    case []:
      []
    case +h <> t:
      List.append(&2, String, roots.one(h), roots(t))

# the walk from every committed source. A listing git could not give is a
# walk refused before its first step.
def walk.of(+led: M.Read, listing: W.Listing, +js: List<&2, W.Judged>) -> Walk:
  match listing:
    case W.Unlisted{why}:
      Walk{[], [], [], why}
    case W.Listed{fs}:
      walk(U32.to_nat(100000), L.ledger.read(led), js, Walk{roots(fs), [], [], ""})

# why a plain lock cannot copy the ledger's tool pins, or "" when it can. A
# ledger that does not parse is refused here too.
def need.why(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{why}:
      "ez: " ++ M.show(M.Bad{why})
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _ds, ts} = m
      Pin.gaps(ts)

# ---------------------------------------------------------------------------
# what the lock may hold

# a char the lock's TOML cannot carry inside a quoted key or value: eztoml
# neither writes nor reads escapes
def char.bad(+ch: Char) -> Bool:
  Bool.or(Char.is_eq(ch, '"'), Bool.or(Char.is_eq(ch, '\\'), Char.is_eq(ch, '\n')))

# whether a key or value can be written as it is
def clean(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      +rest = clean(t)
      Bool.and(Bool.not(char.bad(h)), rest)

# whether every string in a list can be written as it is
def clean.all(ss: List<&2, String>) -> Bool:
  match ss:
    case []:
      True{}
    case h <> t:
      +rest = clean.all(t)
      Bool.and(clean(h), rest)

# every value a package's source writes
def src.values(source: L.Src) -> List<&2, String>:
  match source:
    case L.Hub{}:
      []
    case L.Git{url, rev, entry, root, nar, tag}:
      [url, rev, entry, root, nar, tag]

# every path and sum a package's files write
def file.values(fs: List<&2, K.File>) -> List<&2, String>:
  match fs:
    case []:
      []
    case K.File{at, sum} <> t:
      at <> (sum <> file.values(t))

# every hash, key and value a package writes
def pack.values(pack: L.Pack) -> List<&2, String>:
  L.Pack{hash, src, fs} = pack
  hash <> List.append(&2, String, src.values(src), file.values(fs))

# whether every package can be written, and no hash is written twice
def packs.ok(ps: List<&2, L.Pack>) -> Bool:
  match ps:
    case []:
      True{}
    case +h <> +t:
      +rest = packs.ok(t)
      Bool.and(Bool.and(clean.all(pack.values(h)), Bool.not(L.has(t, L.pack.hash(h)))),
        rest)

# every name, key and value a tool pin writes
def tool.values(pin: M.Tool) -> List<&2, String>:
  M.Tool{n, e, b, s} = pin
  match s:
    case M.Hub{}:
      [n, e, b]
    case M.Git{url, rev, tag, root, nar, _vend}:
      [n, e, b, url, rev, tag, root, nar]

# whether every tool pin can be written
def tools.ok(ts: List<&2, M.Tool>) -> Bool:
  match ts:
    case []:
      True{}
    case h <> t:
      +rest = tools.ok(t)
      Bool.and(clean.all(tool.values(h)), rest)

# whether a lock can be written so that it reads back: every hash is written
# once, and no hash, key or value holds `"`, `\` or a newline. The planner
# refuses a lock that is not, so every lock ez writes is one of these.
def lockable(ps: List<&2, L.Pack>, ts: List<&2, M.Tool>, hub: String) -> Bool:
  Bool.and(clean(hub), Bool.and(packs.ok(ps), tools.ok(ts)))

# ---------------------------------------------------------------------------
# the lock's text, or why there is none

# what a plain lock decides: the text of ez.lock.toml, or why it refuses
type Doc is Data:
  Doc{text: String}
  Stop{why: String}

# a lock that can be written, written
def doc.lockable(ok: Bool, +hub: String, packs: List<&2, L.Pack>, ts: List<&2, M.Tool>) -> Doc:
  match ok:
    case True{}:
      Doc{L.render.tools(ts, hub, packs)}
    case False{}:
      Stop{"ez: ez.lock.toml cannot be written: a hash repeats, or a hash, path or value holds a quote, a backslash or a newline"}

# a walk with nothing left to ask is the lock. One that still has a question
# is a World the interpreter did not finish, and is refused rather than
# guessed at.
def doc.asks(asks: List<&2, String>, +hub: String, +packs: List<&2, L.Pack>, +ts: List<&2, M.Tool>) -> Doc:
  match asks:
    case []:
      doc.lockable(lockable(packs, ts, hub), hub, packs, ts)
    case h <> _t:
      Stop{"ez: " ++ h ++ " was never read, so there is nothing to lock it from"}

# a refusal wins over everything after it
def doc.bad(
  clean: Bool,
  +bad: String,
  asks: List<&2, String>,
  +hub: String,
  packs: List<&2, L.Pack>,
  ts: List<&2, M.Tool>
) -> Doc:
  match clean:
    case True{}:
      doc.asks(asks, hub, packs, ts)
    case False{}:
      Stop{bad}

# the walk's result
def doc.walk(wk: Walk, +hub: String, ts: List<&2, M.Tool>) -> Doc:
  Walk{_queue, packs, asks, +bad} = wk
  doc.bad(String.is_empty(bad), bad, asks, hub, packs, ts)

# a tool pin a plain lock would have to fill stops it before the walk counts
def doc.gap(clean: Bool, +gap: String, wk: Walk, +hub: String, ts: List<&2, M.Tool>) -> Doc:
  match clean:
    case True{}:
      doc.walk(wk, hub, ts)
    case False{}:
      Stop{gap}

# plain `ez lock` over a parsed ledger
def decide.led(+led: M.Read, listing: W.Listing, +js: List<&2, W.Judged>) -> Doc:
  +gap = need.why(led)
  doc.gap(String.is_empty(gap), gap, walk.of(led, listing, js), M.hub_of(led),
    M.tools_of(led))

# plain `ez lock` over what the lock may depend on
def decide(ins: W.Inputs) -> Doc:
  W.Inputs{ledger, listing, js} = ins
  decide.led(W.parsed(ledger), listing, js)

# ---------------------------------------------------------------------------
# the plan

# where a package is laid: `.ez/lib`, which is committed for a vendored
# dependency, or `$BEND_LIB`, which is a cache
type Place is Data:
  Committed{}
  Cache{}

# one thing the interpreter does. A `Lay` writes each file under
# `<place>/<hash>`, in order; the manifest comes last, so a tree that has one
# is a tree that finished.
type Effect is Data:
  Write{path: String, text: String}
  Lay{place: Place, hash: String, files: List<&2, W.Source>}
  Say{text: String}

# how the command ends: exit 0, or exit 1 with the reason
type Outcome is Data:
  Success{}
  Refused{why: String}

# the effects, in order, and how the command ends after them
type Plan is Data:
  Plan{effects: List<&2, Effect>, outcome: Outcome}

# the questions still open, or the plan once there are none
type Step is Data:
  Asking{asks: List<&2, W.Ask>}
  Run{plan: Plan}

# what a plan leaves at one path: nothing written, or this text
type Wrote is Data:
  Kept{}
  Put{text: String}

# the lock's path, which is fixed
def lockfile() -> String:
  "ez.lock.toml"

# every hash a clone answered: those are the trees a lock lays under BEND_LIB
# for the build that follows
def cloned.how(how: W.How, +hash: String) -> List<&2, String>:
  match how:
    case W.Lib{}:
      []
    case W.Clone{_nar}:
      [hash]
    case W.Served{}:
      []

def cloned.one(+hash: String, answer: W.Answer) -> List<&2, String>:
  match answer:
    case W.Miss{_why}:
      []
    case W.Got{how, _manifest, _ss}:
      cloned.how(how, hash)

# every hash a clone answered, in the order they were answered
def cloned(rs: List<&2, W.Reply>) -> List<&2, String>:
  match rs:
    case []:
      []
    case W.Reply{ask, answer} <> t:
      List.append(&2, String, cloned.one(W.ask.hash(ask), answer), cloned(t))

# each file with its text, as it is laid
def laid(fs: List<&2, K.File>, ss: List<&2, String>) -> List<&2, W.Source>:
  match fs ss:
    case Nil{} Nil{}:
      []
    case Nil{} Con{_s, _t}:
      []
    case Con{_f, _g} Nil{}:
      []
    case Con{f, g} Con{s, t}:
      W.Source{K.file.at(f), s} <> laid(g, t)

# a checked tree laid in the cache, ahead of what follows
def lay.verdict(verdict: W.Verdict, +hash: String, rest: List<&2, Effect>) -> List<&2, Effect>:
  match verdict:
    case W.No{_why}:
      rest
    case W.Ok{+fs, ss}:
      Lay{Cache{}, hash, List.append(&2, W.Source, laid(fs, ss),
        [W.Source{"manifest", K.manifest_of(fs)}])} <> rest

def lay.pick(hit: Bool, verdict: W.Verdict, +hash: String, rest: List<&2, Effect>) -> List<&2, Effect>:
  match hit:
    case True{}:
      lay.verdict(verdict, hash, rest)
    case False{}:
      rest

# every cloned tree that passed its checks, laid ahead of what follows
def lays(+cs: List<&2, String>, js: List<&2, W.Judged>, rest: List<&2, Effect>) -> List<&2, Effect>:
  match js:
    case []:
      rest
    case W.Judged{+h, v} <> t:
      lay.pick(L.seen.holds(cs, h), v, h, lays(cs, t, rest))

# the plan for what was decided. A refusal has no effect at all, so a refused
# lock writes nothing and lays nothing; its reason is how it ends.
def made(cs: List<&2, String>, js: List<&2, W.Judged>, doc: Doc) -> Plan:
  match doc:
    case Doc{text}:
      Plan{lays(cs, js, [Write{lockfile(), text}]), Success{}}
    case Stop{why}:
      Plan{[], Refused{why}}

# plain `ez lock` over a World: every package checked once, and the plan
def plan(world: W.World) -> Plan:
  W.World{_args, +ledger, listing, +replies} = world
  +js = W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)
  made(cloned(replies), js, decide(W.Inputs{ledger, listing, js}))

# whether what was decided is a refusal
def refuses.doc(doc: Doc) -> Bool:
  match doc:
    case Doc{_text}:
      False{}
    case Stop{_why}:
      True{}

# whether plain `ez lock` refuses on a World
def refuses(world: W.World) -> Bool:
  refuses.doc(decide(W.inputs(world)))

# the packages plain `ez lock` resolves on a World, which are the packages its
# lock renders when it writes one
def packs(world: W.World) -> List<&2, L.Pack>:
  W.World{_args, +ledger, listing, replies} = world
  walk.packs(walk.of(W.parsed(ledger), listing,
    W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)))

# ---------------------------------------------------------------------------
# what a plan writes

# one effect's part in what a path is left holding, with what the effects
# after it leave already known. A later write wins.
def put.one(effect: Effect, +path: String, rest: Wrote) -> Wrote:
  match effect:
    case Write{at, text}:
      match rest:
        case Kept{}:
          Bool.pick(Wrote, String.eq(at, path), Put{text}, Kept{})
        case Put{later}:
          Put{later}
    case Lay{_place, _hash, _files}:
      rest
    case Say{_text}:
      rest

# what a list of effects leaves at a path
def put.in(es: List<&2, Effect>, +path: String) -> Wrote:
  match es:
    case []:
      Kept{}
    case e <> t:
      put.one(e, path, put.in(t, path))

# what a plan leaves at a path
def put.plan(pl: Plan, +path: String) -> Wrote:
  Plan{es, _outcome} = pl
  put.in(es, path)

# the bytes plain `ez lock` writes to a path on a World, or Kept when it
# writes none
def put(world: W.World, +path: String) -> Wrote:
  put.plan(plan(world), path)

# whether an effect writes, lays or removes anything
def writes.one(effect: Effect) -> Bool:
  match effect:
    case Write{_at, _text}:
      True{}
    case Lay{_place, _hash, _files}:
      True{}
    case Say{_text}:
      False{}

# whether a plan writes, lays or removes anything
def writes.in(es: List<&2, Effect>) -> Bool:
  match es:
    case []:
      False{}
    case e <> t:
      +rest = writes.in(t)
      Bool.or(writes.one(e), rest)

# whether a plan writes, lays or removes anything at all
def writes(pl: Plan) -> Bool:
  Plan{es, _outcome} = pl
  writes.in(es)

# ---------------------------------------------------------------------------
# what is still to ask

# an answer as far as `wants` needs it: the texts it may import from, taken
# as they are and not checked, or the miss
def scan.one(answer: W.Answer) -> W.Verdict:
  match answer:
    case W.Miss{why}:
      W.No{why}
    case W.Got{_how, _manifest, ss}:
      W.Ok{[], ss}

# every reply, scanned
def scan(rs: List<&2, W.Reply>) -> List<&2, W.Judged>:
  match rs:
    case []:
      []
    case W.Reply{ask, answer} <> t:
      W.Judged{W.ask.hash(ask), scan.one(answer)} <> scan(t)

# each hash still to ask about, as the question for it
def asks.of(hs: List<&2, String>, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  match hs:
    case []:
      []
    case +h <> t:
      W.Pkg{h, L.origin(orgs, h), hub} <> asks.of(t, orgs, hub)

# nothing more is asked once the lock is known to refuse
def wants.bad(clean: Bool, hs: List<&2, String>, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      asks.of(List.reverse(&2, String, hs), orgs, hub)
    case False{}:
      []

def wants.walk(wk: Walk, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  Walk{_queue, _packs, hs, +bad} = wk
  wants.bad(String.is_empty(bad), hs, orgs, hub)

def wants.gap(clean: Bool, wk: Walk, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      wants.walk(wk, orgs, hub)
    case False{}:
      []

def wants.led(+led: M.Read, listing: W.Listing, +js: List<&2, W.Judged>) -> List<&2, W.Ask>:
  wants.gap(String.is_empty(need.why(led)), walk.of(led, listing, js),
    L.ledger.read(led), M.hub_of(led))

# the questions a World still leaves open: every package the walk reaches
# that nothing has answered for yet. None once the lock is known to refuse.
def wants(world: W.World) -> List<&2, W.Ask>:
  W.World{_args, ledger, listing, replies} = world
  wants.led(W.parsed(ledger), listing, scan(replies))

# the questions still open, or the plan once there are none
def step.of(asks: List<&2, W.Ask>, world: W.World) -> Step:
  match asks:
    case []:
      Run{plan(world)}
    case h <> t:
      Asking{h <> t}

# what the interpreter does next on a World
def step(+world: W.World) -> Step:
  step.of(wants(world), world)
