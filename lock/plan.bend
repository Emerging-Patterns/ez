# lock/plan: `ez lock` as a pure planner. It reads a World (lock/world.bend)
# and returns either the questions it still needs answered (`step`) or a Plan:
# the effects to run and how the command ends (`plan`). The interpreter
# (lock/run.bend) loops on `step`, answering each question by IO, until
# nothing is left to ask, then executes the plan.
#
# Under `--upgrade` the upgrade's questions come first (lock/up.bend): what
# the remote says each selected pin moves to. Once they are answered, the
# lock is planned exactly as a plain lock is, over the ledger the upgrade
# leaves rather than ez.toml as it was, and the upgrade's writes go around it
# in one plan: trees laid, ez.toml written once, `.gitignore`, the rewritten
# sources, the committed trees that moved removed, and the lock last.
#
# `wants` only scans the answers it has for imports; `plan` checks every
# package once, so a lock pays for each file's SHA-256 once however deep the
# import graph is. A package that fails a check may make `wants` ask for more
# than the lock needs, which costs a fetch and changes nothing, since `plan`
# refuses it.
#
# A named import, `import <name>@<version>/...`, is a hub package too
# (EZ-HUB-3). One the project's own sources import must be a dependency
# ez.toml records by that name, and resolves to the hash ez.toml records
# beside it; one a package imports resolves the same way when ez.toml names
# it, then by the lock being rewritten, and only then by asking the hub, once
# (EZ-HUB-2). The package it resolves to is walked and checked like any hub
# package, and the lock records every name it resolved under `[names]`.
#
# What a lock decides depends on a World only through `W.inputs`: the ledger
# it is made from, the upgrade's refusal if any, the committed sources, and
# the verdict on every answer. How a tree arrived only decides whether it is
# laid under BEND_LIB for the build that follows, which is a cache and not
# something the lock records.
import Base
import ./world.bend as W
import ./up.bend as Up
import ./lock.bend as L
import ../manifest/manifest.bend as M
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
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

# one package, by its verdict. Its imports are queued by hash, and by the
# hash the table of names gives each name it imports.
def step.verdict(
  verdict: W.Verdict,
  +ns: List<&2, L.Name>,
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
      Walk{List.append(&2, String, rest, L.kids.in(ns, ss)), L.Pack{hash, src, fs} <> packs,
        asks, bad}
    case W.Named{_names}:
      Walk{rest, packs, asks, first(bad, "ez: " ++ hash ++ " is imported as a package, and it is not one")}

# one package, asked about when nothing has answered for it yet
def step.look(
  found: Look,
  +ns: List<&2, L.Name>,
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
      step.verdict(v, ns, src, hash, rest, packs, asks, bad)

# a hash already resolved, or already asked about, is passed over
def step.pick(
  seen: Bool,
  +orgs: List<&2, L.Origin>,
  +ns: List<&2, L.Name>,
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
      step.look(look(js, hash), ns, L.origin(orgs, hash), hash, rest, packs, asks, bad)

# the next hash of the queue, or the walk as it is when the queue is empty
def step.pop(
  +orgs: List<&2, L.Origin>,
  +ns: List<&2, L.Name>,
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
      step.pick(Bool.or(L.has(packs, h), L.seen.holds(asks, h)), orgs, ns, js, h, t,
        packs, asks, bad)

# one step of the walk
def walk.step(+orgs: List<&2, L.Origin>, +ns: List<&2, L.Name>, +js: List<&2, W.Judged>, wk: Walk) -> Walk:
  Walk{queue, packs, asks, bad} = wk
  step.pop(orgs, ns, js, queue, packs, asks, bad)

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
def walk(fuel: Nat, +orgs: List<&2, L.Origin>, +ns: List<&2, L.Name>, +js: List<&2, W.Judged>, +wk: Walk) -> Walk:
  match fuel:
    case 0n:
      walk.out(walk.done(wk), wk)
    case 1n+f:
      walk.more(walk.done(wk), wk, now => walk(f, orgs, ns, js, walk.step(orgs, ns, js, now)))

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

# every name one committed source imports, outside `.ez/`
def roots.named.one(+src: W.Source) -> List<&2, String>:
  W.Source{at, text} = src
  Bool.pick(List<&2, String>, String.starts_with(at, ".ez/"), [],
    L.named(K.scan.mods(K.scan(text))))

# every name the committed sources import. Each must be one ez.toml records
# a dependency by.
def roots.named(fs: List<&2, W.Source>) -> List<&2, String>:
  match fs:
    case []:
      []
    case +h <> t:
      List.append(&2, String, roots.named.one(h), roots.named(t))

# the table of names a lock resolves names by: those ez.toml records, each
# with the hash beside it, first, then those the answers resolve, the lock
# being rewritten's before the hub's
def table(+led: M.Read, js: List<&2, W.Judged>) -> List<&2, L.Name>:
  List.append(&2, L.Name, L.ledger.names(led), W.names.of(js))

# the walk from every committed source: every package they import by hash,
# and every one they import by a name the table resolves. A listing git
# could not give is a walk refused before its first step.
def walk.of(+led: M.Read, listing: W.Listing, +ns: List<&2, L.Name>, +js: List<&2, W.Judged>) -> Walk:
  match listing:
    case W.Unlisted{why}:
      Walk{[], [], [], why}
    case W.Listed{+fs}:
      walk(U32.to_nat(100000), L.ledger.read(led), ns, js,
        Walk{List.append(&2, String, roots(fs), L.name.hashes(ns, roots.named(fs))), [], [], ""})

# the committed sources a listing holds, none when git could not list them
def listing.files(listing: W.Listing) -> List<&2, W.Source>:
  match listing:
    case W.Unlisted{_why}:
      []
    case W.Listed{fs}:
      fs

# the texts of a package the walk resolved, as its verdict holds them
def pack.srcs(found: Look) -> List<&2, String>:
  match found:
    case Absent{}:
      []
    case Found{v}:
      match v:
        case W.Ok{_fs, ss}:
          ss
        case _:
          []

# every name the packages a walk resolved import
def packs.named(+js: List<&2, W.Judged>, ps: List<&2, L.Pack>) -> List<&2, String>:
  match ps:
    case []:
      []
    case +h <> t:
      List.append(&2, String, L.kids.named(pack.srcs(look(js, L.pack.hash(h)))),
        packs.named(js, t))

# every name a lock needs resolved: those the committed sources import, then
# those the packages it reaches import
def needed(listing: W.Listing, +js: List<&2, W.Judged>, ps: List<&2, L.Pack>) -> List<&2, String>:
  List.append(&2, String, roots.named(listing.files(listing)), packs.named(js, ps))

# why a plain lock cannot copy the ledger's tool pins, or "" when it can. A
# ledger that does not parse is refused here too.
def need.why(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{why}:
      "ez: " ++ M.show(M.Bad{why})
    case M.Good{m}:
      M.Manifest{_n, _e, _b, _h, _pa, _pv, _ds, ts} = m
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

# whether a file path holds no `=`. A path is written as a quoted key, and
# `bootstrap.sh`, which reads the lock without ez, cuts a pair line at its
# first `=`, so a path holding one would read back there as another path with
# another sum. eztoml 0.4 reads a quoted key whole; the restriction lifts when
# bootstrap.sh does too.
def path.eqless(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      +rest = path.eqless(t)
      Bool.and(Bool.not(Char.is_eq(h, '=')), rest)

# whether no file path of a package holds `=`
def paths.ok(fs: List<&2, K.File>) -> Bool:
  match fs:
    case []:
      True{}
    case K.File{at, _sum} <> t:
      +rest = paths.ok(t)
      Bool.and(path.eqless(at), rest)

# whether every package can be written, and no hash is written twice
def packs.ok(ps: List<&2, L.Pack>) -> Bool:
  match ps:
    case []:
      True{}
    case +h <> +t:
      +rest = packs.ok(t)
      Bool.and(Bool.and(paths.ok(L.pack.files(h)),
        Bool.and(clean.all(pack.values(h)), Bool.not(L.has(t, L.pack.hash(h))))),
        rest)

# every name, key and value a tool pin writes
def tool.values(pin: M.Tool) -> List<&2, String>:
  M.Tool{n, e, b, s} = pin
  match s:
    case M.Hub{_named}:
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
# once, no hash, key or value holds `"`, `\` or a newline, and no file path
# holds `=` (eztoml#24, above). The planner
# refuses a lock that is not, so every lock ez writes is one of these.
def lockable(ps: List<&2, L.Pack>, ts: List<&2, M.Tool>, hub: String) -> Bool:
  Bool.and(clean(hub), Bool.and(packs.ok(ps), tools.ok(ts)))

# the first path among a package's files that holds `=`, or "" when none
# does. A path that holds one is not empty, so "" is never such a path.
def path.eq.pick(ok: Bool, at: String, rest: String) -> String:
  match ok:
    case True{}:
      rest
    case False{}:
      at

def path.eq.first(fs: List<&2, K.File>) -> String:
  match fs:
    case []:
      ""
    case K.File{+at, _sum} <> t:
      path.eq.pick(path.eqless(at), at, path.eq.first(t))

# why a package with such a path cannot be locked, naming it and the path
def path.eq.why(+hash: String, +at: String) -> String:
  "ez: ez.lock.toml cannot be written: package " ++ hash ++ " has a file " ++
    at ++ " whose path holds `=`, which the lock's TOML reader would cut the" ++
    " key at (https://github.com/Emerging-Patterns/eztoml/issues/24)"

# the reason for the first package with such a path, or the rest's
def packs.eq.pick(none: Bool, +hash: String, +at: String, rest: String) -> String:
  match none:
    case True{}:
      rest
    case False{}:
      path.eq.why(hash, at)

# why the first package with a path holding `=` cannot be locked, or "" when
# no package has one
def packs.eq(ps: List<&2, L.Pack>) -> String:
  match ps:
    case []:
      ""
    case L.Pack{+hash, _src, fs} <> t:
      +at = path.eq.first(fs)
      packs.eq.pick(String.is_empty(at), hash, at, packs.eq(t))

# the reason a lock that is not `lockable` gives: the package and path when a
# path holds `=`, which is the one case a clean-looking lock hides
def lockable.pick(none: Bool, why: String) -> String:
  match none:
    case True{}:
      "ez: ez.lock.toml cannot be written: a hash repeats, or a hash, path or value holds a quote, a backslash or a newline"
    case False{}:
      why

def lockable.why(ps: List<&2, L.Pack>) -> String:
  +why = packs.eq(ps)
  lockable.pick(String.is_empty(why), why)

# whether every name the lock records can be written so that it reads back:
# a name is written as a quoted key and its hash as a value, the way a
# package's file is, so it is held to what a file is held to
def names.ok(ns: List<&2, L.Name>) -> Bool:
  +fs = L.name.files(ns)
  Bool.and(paths.ok(fs), clean.all(file.values(fs)))

# whether a lock with names can be written so that it reads back
def lockable.named(ns: List<&2, L.Name>, ps: List<&2, L.Pack>, ts: List<&2, M.Tool>, hub: String) -> Bool:
  Bool.and(names.ok(ns), lockable(ps, ts, hub))

# the reason a lock with names that is not lockable gives
def lockable.why.pick(ok: Bool, ps: List<&2, L.Pack>) -> String:
  match ok:
    case True{}:
      lockable.why(ps)
    case False{}:
      "ez: ez.lock.toml cannot be written: a name, or the hash ez.toml records for it, holds `=`, a quote, a backslash or a newline"

def lockable.why.named(ns: List<&2, L.Name>, ps: List<&2, L.Pack>) -> String:
  lockable.why.pick(names.ok(ns), ps)

# ---------------------------------------------------------------------------
# the names a lock needs

# a name, when it is the first the search wants, or the rest's
def names.missing.pick(gone: Bool, +nv: String, rest: Unit -> String) -> String:
  match gone:
    case True{}:
      nv
    case False{}:
      rest(Unit{})

# the first name of a list the hub rules out, or "" when it rules them all in
def names.ruled(nvs: List<&2, String>) -> String:
  match nvs:
    case []:
      ""
    case +h <> t:
      names.missing.pick(Bool.not(K.name.ok(h)), h, _u => names.ruled(t))

# the first name of a list the table does not resolve, or "" when it
# resolves them all
def names.missing(+ns: List<&2, L.Name>, nvs: List<&2, String>) -> String:
  match nvs:
    case []:
      ""
    case +h <> t:
      names.missing.pick(String.is_empty(L.name.find(ns, h)), h, _u => names.missing(ns, t))

# why a name nothing resolved stops the lock: what its answer said, or that
# it was never asked
def names.open.why(found: Look, +nv: String) -> String:
  match found:
    case Found{v}:
      match v:
        case W.No{why}:
          why
        case _:
          "ez: " ++ nv ++ " was never resolved, so there is nothing to lock it from"
    case Absent{}:
      "ez: " ++ nv ++ " was never resolved, so there is nothing to lock it from"

# why a name the project imports and ez.toml does not record stops the lock
def names.unledgered.why(+nv: String) -> String:
  "ez: " ++ nv ++ " is imported, and ez.toml records no dependency by that name; " ++
    "a named package is recorded as `hub = \"" ++ nv ++ "\"` beside the hash it names"

# a reason, or when there is none the next one, looked at only then
def why.then.at(none: Bool, why: String, rest: Unit -> String) -> String:
  match none:
    case True{}:
      rest(Unit{})
    case False{}:
      why

def why.then(+why: String, rest: Unit -> String) -> String:
  why.then.at(String.is_empty(why), why, rest)

# no reason when no name is at fault, and the fault's otherwise
def why.missing.at(none: Bool, reason: Unit -> String) -> String:
  match none:
    case True{}:
      ""
    case False{}:
      reason(Unit{})

def why.missing(+nv: String, reason: Unit -> String) -> String:
  why.missing.at(String.is_empty(nv), reason)

# why the names a lock needs stop it, or "" when they do not: a name the hub
# rules out, as bend refuses it; a name the project imports that ez.toml does
# not record, which is the lock's own rule, since only a dependency ez.toml
# records vouches for where a name came from; and a name nothing resolved
def names.why(
  +lns: List<&2, L.Name>,
  +ns: List<&2, L.Name>,
  +js: List<&2, W.Judged>,
  +roots: List<&2, String>,
  +need: List<&2, String>
) -> String:
  +bad = names.ruled(need)
  why.then(why.missing(bad, _u => K.unnamed.why(bad)), _v =>
    why.then(why.missing(names.missing(lns, roots), _w =>
        names.unledgered.why(names.missing(lns, roots))), _x =>
      why.missing(names.missing(ns, need), _y =>
        names.open.why(look(js, names.missing(ns, need)), names.missing(ns, need)))))

# ---------------------------------------------------------------------------
# the lock's text, or why there is none

# what a plain lock decides: the text of ez.lock.toml, or why it refuses
type Doc is Data:
  Doc{text: String}
  Stop{why: String}

# a lock that can be written, written, with the names it resolved
def doc.lockable(
  ok: Bool,
  +ns: List<&2, L.Name>,
  +hub: String,
  packs: List<&2, L.Pack>,
  ts: List<&2, M.Tool>
) -> Doc:
  match ok:
    case True{}:
      Doc{L.render.names(ns, ts, hub, packs)}
    case False{}:
      Stop{lockable.why.named(ns, packs)}

# a walk with nothing left to ask is the lock. One that still has a question
# is a World the interpreter did not finish, and is refused rather than
# guessed at.
def doc.asks(
  asks: List<&2, String>,
  +ns: List<&2, L.Name>,
  +hub: String,
  +packs: List<&2, L.Pack>,
  +ts: List<&2, M.Tool>
) -> Doc:
  match asks:
    case []:
      doc.lockable(lockable.named(ns, packs, ts, hub), ns, hub, packs, ts)
    case h <> _t:
      Stop{"ez: " ++ h ++ " was never read, so there is nothing to lock it from"}

# the names settled: a name that stops the lock stops it, and otherwise the
# lock records each name it needed with the hash the table gives it
def doc.named(
  clean: Bool,
  why: String,
  asks: List<&2, String>,
  +ns: List<&2, L.Name>,
  +need: List<&2, String>,
  +hub: String,
  packs: List<&2, L.Pack>,
  ts: List<&2, M.Tool>
) -> Doc:
  match clean:
    case True{}:
      doc.asks(asks, L.name.pairs(ns, need), hub, packs, ts)
    case False{}:
      Stop{why}

# a refusal wins over everything after it
def doc.bad(
  clean: Bool,
  +bad: String,
  asks: List<&2, String>,
  +led: M.Read,
  listing: W.Listing,
  +ns: List<&2, L.Name>,
  +js: List<&2, W.Judged>,
  +packs: List<&2, L.Pack>
) -> Doc:
  match clean:
    case True{}:
      +fs = listing.files(listing)
      +need = List.append(&2, String, roots.named(fs), packs.named(js, packs))
      +why = names.why(L.ledger.names(led), ns, js, roots.named(fs), need)
      doc.named(String.is_empty(why), why, asks, ns, need, M.hub_of(led), packs,
        M.tools_of(led))
    case False{}:
      Stop{bad}

# the walk's result
def doc.walk(wk: Walk, +led: M.Read, listing: W.Listing, +ns: List<&2, L.Name>, +js: List<&2, W.Judged>) -> Doc:
  Walk{_queue, packs, asks, +bad} = wk
  doc.bad(String.is_empty(bad), bad, asks, led, listing, ns, js, packs)

# a tool pin a plain lock would have to fill stops it before the walk counts
def doc.gap(
  clean: Bool,
  +gap: String,
  wk: Walk,
  +led: M.Read,
  listing: W.Listing,
  +ns: List<&2, L.Name>,
  +js: List<&2, W.Judged>
) -> Doc:
  match clean:
    case True{}:
      doc.walk(wk, led, listing, ns, js)
    case False{}:
      Stop{gap}

# plain `ez lock` over a parsed ledger
def decide.led(+led: M.Read, +listing: W.Listing, +js: List<&2, W.Judged>) -> Doc:
  +gap = need.why(led)
  +ns = table(led, js)
  doc.gap(String.is_empty(gap), gap, walk.of(led, listing, ns, js), led, listing, ns, js)

# an upgrade that refused, or still asks, stops the lock before anything else
def decide.stop(clean: Bool, +stop: String, +led: M.Read, listing: W.Listing, +js: List<&2, W.Judged>) -> Doc:
  match clean:
    case True{}:
      decide.led(led, listing, js)
    case False{}:
      Stop{stop}

# `ez lock` over what the lock may depend on
def decide(ins: W.Inputs) -> Doc:
  W.Inputs{+ledger, +stop, listing, +js} = ins
  decide.stop(String.is_empty(stop), stop, ledger, listing, js)

# ---------------------------------------------------------------------------
# the plan

# where a package is laid: `.ez/lib`, which is committed for a vendored
# dependency, or `$BEND_LIB`, which is a cache
type Place is Data:
  Committed{}
  Cache{}

# one thing the interpreter does. A `Lay` writes each file under
# `<place>/<hash>`, in order; the manifest comes last, so a tree that has one
# is a tree that finished. A `Drop` removes `.ez/lib/<hash>`, a committed tree
# an upgrade moved off. A `Name` writes `$BEND_LIB/names/<nv>` holding the
# hash and a newline, the file bend reads a name's hash from before it would
# ask the hub (EZ-HUB-4). A `Say` is a line a person is told.
type Effect is Data:
  Write{path: String, text: String}
  Lay{place: Place, hash: String, files: List<&2, W.Source>}
  Drop{hash: String}
  Say{text: String}
  Name{nv: String, hash: String}

# how the command ends: exit 0, or exit 1 with the reason
type Outcome is Data:
  Success{}
  Refused{why: String}

# the effects, in order, and how the command ends after them
type Plan is Data:
  Plan{effects: List<&2, Effect>, outcome: Outcome}

# the status a command exits with (EZ-OUT-1): 0 when it succeeds, 1 when it
# refuses. Every planner's plan ends with an Outcome, and the interpreter
# exits with this status of it (`Run.end`), so this is the one place the
# mapping lives.
def status(outcome: Outcome) -> U32:
  match outcome:
    case Success{}:
      0
    case Refused{_why}:
      1

# the status of a command that refused, or did not
def status.of(refused: Bool) -> U32:
  Bool.pick(U32, refused, 1, 0)

# what a command that ends is said to have ended on: nothing when it
# succeeded, and the reason when it refused
def why(outcome: Outcome) -> String:
  match outcome:
    case Success{}:
      ""
    case Refused{why}:
      why

# the status a plan ends with
def code(pl: Plan) -> U32:
  Plan{_es, o} = pl
  status(o)

# one of the upgrade's questions, as the upgrade looks its answer up (`ask`,
# with the source the ledger records) and as git is asked it (`git`, with
# that source anchored at the directory the lock runs in, `Up.anchor`). The
# interpreter answers `git` and records the answer under `ask`.
type Query is Data:
  Query{ask: Up.Ask, git: Up.Ask}

# the questions still open, the lock's and the upgrade's, or the plan once
# there are none. The lock's are about packages, and, apart from them, about
# names: the lock being rewritten, and what the hub says a name names.
type Step is Data:
  Asking{asks: List<&2, W.Ask>, ups: List<&2, Query>, names: List<&2, W.Ask>}
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
    case W.Said{_text}:
      []
    case W.Locked{_text}:
      []

# every hash a clone answered, in the order they were answered
def cloned(rs: List<&2, W.Reply>) -> List<&2, String>:
  match rs:
    case []:
      []
    case W.Reply{ask, answer} <> t:
      List.append(&2, String, cloned.one(W.ask.hash(ask), answer), cloned(t))

# where a tree is laid: under `.ez/lib`, committed, when the ledger the lock
# is made from vendors its hash, and under BEND_LIB otherwise
def place.of(vend: Bool) -> Place:
  match vend:
    case True{}:
      Committed{}
    case False{}:
      Cache{}

# a checked tree laid, ahead of what follows: its files with their texts,
# then the manifest of those texts, which is the manifest whose name the
# verdict checked (`W.body.laid`)
def lay.verdict(verdict: W.Verdict, place: Place, +hash: String, rest: List<&2, Effect>) -> List<&2, Effect>:
  match verdict:
    case W.No{_why}:
      rest
    case W.Ok{fs, ss}:
      +ls = W.laid(fs, ss)
      Lay{place, hash, List.append(&2, W.Source, ls,
        [W.Source{"manifest", W.manifest(ls)}])} <> rest
    case W.Named{_ns}:
      rest

def lay.pick(hit: Bool, verdict: W.Verdict, place: Place, +hash: String, rest: List<&2, Effect>) -> List<&2, Effect>:
  match hit:
    case True{}:
      lay.verdict(verdict, place, hash, rest)
    case False{}:
      rest

# every cloned tree that passed its checks, laid ahead of what follows. `vs`
# are the hashes committed under `.ez/lib`; a plain lock has none, and lays
# every tree in the cache.
def lays(
  +cs: List<&2, String>,
  +vs: List<&2, String>,
  js: List<&2, W.Judged>,
  rest: List<&2, Effect>
) -> List<&2, Effect>:
  match js:
    case []:
      rest
    case W.Judged{+h, v} <> t:
      lay.pick(L.seen.holds(cs, h), v, place.of(L.seen.holds(vs, h)), h,
        lays(cs, vs, t, rest))

# a names file for every name a lock records, ahead of what follows, so bend
# reads each name's hash from BEND_LIB and never asks the hub for it
def names.lay(ns: List<&2, L.Name>, rest: List<&2, Effect>) -> List<&2, Effect>:
  match ns:
    case []:
      rest
    case L.Name{nv, hash} <> t:
      Name{nv, hash} <> names.lay(t, rest)

# the lines a person is told, ahead of what follows
def says.of(ss: List<&2, String>, rest: List<&2, Effect>) -> List<&2, Effect>:
  match ss:
    case []:
      rest
    case h <> t:
      Say{h} <> says.of(t, rest)

# the lines a list of effects says, in order
def said.in(es: List<&2, Effect>) -> List<&2, String>:
  match es:
    case []:
      []
    case e <> t:
      match e:
        case Say{text}:
          text <> said.in(t)
        case _:
          said.in(t)

# the lines a plan says, in order, which is what a person is told
def said(pl: Plan) -> List<&2, String>:
  Plan{es, _outcome} = pl
  said.in(es)

# the files the upgrade writes, in order, ahead of what follows
def edits.of(es: List<&2, Up.Edit>, rest: List<&2, Effect>) -> List<&2, Effect>:
  match es:
    case []:
      rest
    case Up.Edit{at, text} <> t:
      Write{at, text} <> edits.of(t, rest)

# the committed trees the upgrade moved off, removed ahead of what follows
def drops.of(ds: List<&2, String>, rest: List<&2, Effect>) -> List<&2, Effect>:
  match ds:
    case []:
      rest
    case h <> t:
      Drop{h} <> drops.of(t, rest)

# the plan for what was decided. A refusal has no effect at all, so a refused
# lock, plain or upgrade, writes nothing, lays nothing and removes nothing; its
# reason is how it ends. A lock that is made runs, in order: what a person is
# told, the trees laid, a names file for every name the lock records (read
# back from the lock's own text, so the files and the lock never disagree),
# the upgrade's files (ez.toml once, `.gitignore`, the rewritten sources), the
# committed trees removed, and the lock last. A plain lock has only the
# trees, the names and the lock.
def made(+nx: Up.Next, cs: List<&2, String>, js: List<&2, W.Judged>, doc: Doc) -> Plan:
  match doc:
    case Doc{+text}:
      Plan{says.of(Up.next.says(nx),
        lays(cs, Up.next.vends(nx), js, names.lay(L.names.read(text),
          edits.of(Up.next.edits(nx),
            edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              drops.of(Up.next.drops(nx), [Write{lockfile(), text}])))))), Success{}}
    case Stop{why}:
      Plan{[], Refused{why}}

# `ez lock` once the upgrade decided: every package checked once, and the plan
def plan.of(+nx: Up.Next, listing: W.Listing, +replies: List<&2, W.Reply>) -> Plan:
  +js = W.judged.of(nx, replies)
  made(nx, cloned(W.replies.of(nx, replies)), js,
    decide(W.Inputs{Up.next.read(nx), Up.next.stop(nx), W.listing.of(nx, listing), js}))

# `ez lock` over a World
def plan(world: W.World) -> Plan:
  W.World{args, +ledger, listing, replies, ups} = world
  plan.of(W.next(args, ledger, ups), listing, replies)

# whether what was decided is a refusal
def refuses.doc(doc: Doc) -> Bool:
  match doc:
    case Doc{_text}:
      False{}
    case Stop{_why}:
      True{}

# whether `ez lock` refuses on a World
def refuses(world: W.World) -> Bool:
  refuses.doc(decide(W.inputs(world)))

# the packages `ez lock` resolves once the upgrade decided
def packs.of(+nx: Up.Next, listing: W.Listing, replies: List<&2, W.Reply>) -> List<&2, L.Pack>:
  +js = W.judged.of(nx, replies)
  walk.packs(walk.of(Up.next.read(nx), W.listing.of(nx, listing),
    table(Up.next.read(nx), js), js))

# the packages `ez lock` resolves on a World, which are the packages its lock
# renders when it writes one
def packs(world: W.World) -> List<&2, L.Pack>:
  W.World{args, +ledger, listing, replies, ups} = world
  packs.of(W.next(args, ledger, ups), listing, replies)

# the ledger model an upgrade renders into ez.toml; ez.toml as it was when
# the upgrade refuses, still asks, or moves nothing, and for a plain lock. The
# upgrade's decisions (EZ-RES-4 to 6 and 8) are stated over it, and hold of
# ez.toml's bytes, which read back as it (EZ-LED-4).
def ledger.next(world: W.World) -> M.Read:
  W.World{args, +ledger, _listing, _replies, ups} = world
  Up.next.model(W.next(args, ledger, ups))

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
    case Drop{_hash}:
      rest
    case Say{_text}:
      rest
    case Name{_nv, _hash}:
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

# the bytes `ez lock` writes to a path on a World, or Kept when it writes
# none
def put(world: W.World, +path: String) -> Wrote:
  put.plan(plan(world), path)

# whether an effect writes, lays or removes anything
def writes.one(effect: Effect) -> Bool:
  match effect:
    case Write{_at, _text}:
      True{}
    case Lay{_place, _hash, _files}:
      True{}
    case Drop{_hash}:
      True{}
    case Say{_text}:
      False{}
    case Name{_nv, _hash}:
      True{}

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
# the trees a plan lays, named (EZ-HASH-3). Law vocabulary for `ez lock`,
# `ez add` and `ez fetch`, which lay trees through the same effect.

# every file of a tree but the last, which a `Lay` writes as the manifest
def front(fs: List<&2, W.Source>) -> List<&2, W.Source>:
  match fs:
    case []:
      []
    case h <> t:
      match t:
        case []:
          []
        case h2 <> t2:
          h <> front(h2 <> t2)

# a file's text
def text.of(src: W.Source) -> String:
  W.Source{_at, text} = src
  text

# the last file's text, "" for no file
def last(fs: List<&2, W.Source>) -> String:
  match fs:
    case []:
      ""
    case h <> t:
      match t:
        case []:
          text.of(h)
        case h2 <> t2:
          last(h2 <> t2)

# whether a laid tree is named by the manifest of the texts it lays: its
# last file is the manifest of the others, each weighed by its own text,
# and its hash is the `0x` name of that manifest
def lay.named(+hash: String, +fs: List<&2, W.Source>) -> Bool:
  +sums = K.files_of(W.weighs(front(fs)))
  Bool.and(String.eq(hash, K.hash_of(sums)), String.eq(last(fs), K.manifest_of(sums)))

# whether an effect that lays a tree lays a named one
def lays.one(effect: Effect) -> Bool:
  match effect:
    case Lay{_place, hash, fs}:
      lay.named(hash, fs)
    case _:
      True{}

# whether every tree a list of effects lays is named by its manifest
def lays.named(es: List<&2, Effect>) -> Bool:
  match es:
    case []:
      True{}
    case h <> t:
      +rest = lays.named(t)
      Bool.and(lays.one(h), rest)

# the effects of a plan
def effects(pl: Plan) -> List<&2, Effect>:
  Plan{es, _outcome} = pl
  es

# ---------------------------------------------------------------------------
# what is still to ask

# an answer as far as `wants` needs it: the texts it may import from, taken
# as they are and not checked, or the miss
def scan.one(+hash: String, +hub: String, answer: W.Answer) -> W.Verdict:
  match answer:
    case W.Miss{why}:
      W.No{why}
    case W.Got{_how, _manifest, ss}:
      W.Ok{[], ss}
    case W.Said{text}:
      W.said(hash, hub, text)
    case W.Locked{text}:
      W.locked(text)

# the hub a question names, "" for the lock's
def ask.hub(ask: W.Ask) -> String:
  match ask:
    case W.Pkg{_hash, _src, hub}:
      hub
    case W.Name{_nv, hub}:
      hub
    case W.Lock{}:
      ""

# every reply, scanned
def scan(rs: List<&2, W.Reply>) -> List<&2, W.Judged>:
  match rs:
    case []:
      []
    case W.Reply{+ask, answer} <> t:
      W.Judged{W.ask.hash(ask), scan.one(W.ask.hash(ask), ask.hub(ask), answer)} <> scan(t)

# a package's source as git is to read it: a path anchored at the directory
# the lock runs in (`Path.anchor`), and a URL or an absolute path as it is. A
# hub package names no source. The lock records the source as the ledger
# gives it; only the question carries this.
def anchor.src(+here: String, src: L.Src) -> L.Src:
  match src:
    case L.Hub{}:
      L.Hub{}
    case L.Git{url, rev, entry, root, nar, tag}:
      L.Git{Path.anchor(here, url), rev, entry, root, nar, tag}

# each hash still to ask about, as the question for it, with its source
# anchored
def asks.of(hs: List<&2, String>, +here: String, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  match hs:
    case []:
      []
    case +h <> t:
      W.Pkg{h, anchor.src(here, L.origin(orgs, h)), hub} <> asks.of(t, here, orgs, hub)

# nothing more is asked once the lock is known to refuse
def wants.bad(
  clean: Bool,
  hs: List<&2, String>,
  +here: String,
  +orgs: List<&2, L.Origin>,
  +hub: String
) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      asks.of(List.reverse(&2, String, hs), here, orgs, hub)
    case False{}:
      []

def wants.walk(wk: Walk, +here: String, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  Walk{_queue, _packs, hs, +bad} = wk
  wants.bad(String.is_empty(bad), hs, here, orgs, hub)

def wants.gap(clean: Bool, wk: Walk, +here: String, +orgs: List<&2, L.Origin>, +hub: String) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      wants.walk(wk, here, orgs, hub)
    case False{}:
      []

def wants.led(+here: String, +led: M.Read, listing: W.Listing, +js: List<&2, W.Judged>) -> List<&2, W.Ask>:
  wants.gap(String.is_empty(need.why(led)), walk.of(led, listing, table(led, js), js), here,
    L.ledger.read(led), M.hub_of(led))

# nothing is asked about packages while the upgrade refuses or still asks
def wants.stop(clean: Bool, +here: String, +led: M.Read, listing: W.Listing, js: List<&2, W.Judged>) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      wants.led(here, led, listing, js)
    case False{}:
      []

# the package questions still open once the upgrade decided
def wants.of(+here: String, +nx: Up.Next, listing: W.Listing, replies: List<&2, W.Reply>) -> List<&2, W.Ask>:
  wants.stop(String.is_empty(Up.next.stop(nx)), here, Up.next.read(nx),
    W.listing.of(nx, listing), scan(W.replies.of(nx, replies)))

# the package questions a World still leaves open: every package the walk
# reaches that nothing has answered for yet. None once the lock is known to
# refuse, and none while the upgrade still asks.
def wants(world: W.World) -> List<&2, W.Ask>:
  W.World{+args, +ledger, listing, replies, ups} = world
  wants.of(W.here.of(args), W.next(args, ledger, ups), listing, replies)

# the upgrade's questions a World still leaves open; none for a plain lock
def wants.up(world: W.World) -> List<&2, Up.Ask>:
  W.World{args, +ledger, _listing, _replies, ups} = world
  Up.next.asks(W.next(args, ledger, ups))

# whether the upgrade has every answer it needs
def answered(world: W.World) -> Bool:
  List.is_empty(&2, Up.Ask, wants.up(world))

# each of the upgrade's questions, with the question git is asked for it
def queries(+here: String, as: List<&2, Up.Ask>) -> List<&2, Query>:
  match as:
    case []:
      []
    case +h <> t:
      Query{h, Up.anchor(here, h)} <> queries(here, t)

# ---------------------------------------------------------------------------
# the names still to resolve

# a name kept among the ones to ask about when it is not one already kept
def names.once.put(dup: Bool, +nv: String, rest: List<&2, String>) -> List<&2, String>:
  match dup:
    case True{}:
      rest
    case False{}:
      nv <> rest

# every name of a list once, each where it first stands
def names.once(nvs: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match nvs:
    case []:
      []
    case +h <> t:
      names.once.put(L.seen.holds(seen, h), h, names.once(t, h <> seen))

# whether nothing has answered for a key
def is.absent(found: Look) -> Bool:
  match found:
    case Absent{}:
      True{}
    case Found{_v}:
      False{}

# whether a name is still to be resolved: the hub rules it in, the table does
# not resolve it, the project does not import it (that one ez.toml must
# record, and the lock refuses it), and nothing has answered for it yet
def name.open(+ns: List<&2, L.Name>, +js: List<&2, W.Judged>, +roots: List<&2, String>, +nv: String) -> Bool:
  Bool.and(K.name.ok(nv), Bool.and(String.is_empty(L.name.find(ns, nv)),
    Bool.and(Bool.not(L.seen.holds(roots, nv)), is.absent(look(js, nv)))))

def names.open.put(open: Bool, +nv: String, rest: List<&2, String>) -> List<&2, String>:
  match open:
    case True{}:
      nv <> rest
    case False{}:
      rest

# every name of a list still to be resolved
def names.open(
  +ns: List<&2, L.Name>,
  +js: List<&2, W.Judged>,
  +roots: List<&2, String>,
  nvs: List<&2, String>
) -> List<&2, String>:
  match nvs:
    case []:
      []
    case +h <> t:
      names.open.put(name.open(ns, js, roots, h), h, names.open(ns, js, roots, t))

# each name as the question the hub is asked about it
def names.asked(+hub: String, nvs: List<&2, String>) -> List<&2, W.Ask>:
  match nvs:
    case []:
      []
    case h <> t:
      W.Name{h, hub} <> names.asked(hub, t)

# the questions for the names still open: none when there are none; the lock
# being rewritten first, since a name it records is not put to the hub
# (EZ-HUB-2); and then each name the lock does not record, once
def names.ask.lock(read: Bool, +hub: String, nvs: List<&2, String>) -> List<&2, W.Ask>:
  match read:
    case True{}:
      names.asked(hub, names.once(nvs, []))
    case False{}:
      [W.Lock{}]

def names.ask(+hub: String, +js: List<&2, W.Judged>, nvs: List<&2, String>) -> List<&2, W.Ask>:
  match nvs:
    case []:
      []
    case h <> t:
      names.ask.lock(Bool.not(is.absent(look(js, W.lockfile()))), hub, h <> t)

def names.wants.bad(
  clean: Bool,
  +led: M.Read,
  listing: W.Listing,
  +ns: List<&2, L.Name>,
  +js: List<&2, W.Judged>,
  packs: List<&2, L.Pack>
) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      names.ask(M.hub_of(led), js,
        names.open(ns, js, roots.named(listing.files(listing)), packs.named(js, packs)))
    case False{}:
      []

# the name questions of a walk, which ask nothing once the lock is known to
# refuse
def names.wants.walk(
  wk: Walk,
  +led: M.Read,
  +listing: W.Listing,
  +ns: List<&2, L.Name>,
  +js: List<&2, W.Judged>
) -> List<&2, W.Ask>:
  Walk{_queue, packs, _asks, +bad} = wk
  names.wants.bad(String.is_empty(bad), led, listing, ns, js, packs)

def names.wants.gap(clean: Bool, +led: M.Read, +listing: W.Listing, +js: List<&2, W.Judged>) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      +ns = table(led, js)
      names.wants.walk(walk.of(led, listing, ns, js), led, listing, ns, js)
    case False{}:
      []

def names.wants.stop(clean: Bool, +led: M.Read, listing: W.Listing, +js: List<&2, W.Judged>) -> List<&2, W.Ask>:
  match clean:
    case True{}:
      names.wants.gap(String.is_empty(need.why(led)), led, listing, js)
    case False{}:
      []

# the name questions still open once the upgrade decided, over the answers
# scanned as `wants` scans them
def names.wants.of(+nx: Up.Next, listing: W.Listing, replies: List<&2, W.Reply>) -> List<&2, W.Ask>:
  names.wants.stop(String.is_empty(Up.next.stop(nx)), Up.next.read(nx),
    W.listing.of(nx, listing), scan(W.replies.of(nx, replies)))

# the name questions a World still leaves open: for every name a package the
# walk reaches imports, that ez.toml does not record and nothing has
# answered for yet, the lock being rewritten, and once it is read, the hub
def wants.names(world: W.World) -> List<&2, W.Ask>:
  W.World{+args, +ledger, listing, replies, ups} = world
  names.wants.of(W.next(args, ledger, ups), listing, replies)

# the package questions still open, or the name questions, or the plan once
# there are none
def step.names(names: List<&2, W.Ask>, +nx: Up.Next, listing: W.Listing, replies: List<&2, W.Reply>) -> Step:
  match names:
    case []:
      Run{plan.of(nx, listing, replies)}
    case h <> t:
      Asking{[], [], h <> t}

def step.pkgs(
  asks: List<&2, W.Ask>,
  names: List<&2, W.Ask>,
  +nx: Up.Next,
  listing: W.Listing,
  replies: List<&2, W.Reply>
) -> Step:
  match asks:
    case []:
      step.names(names, nx, listing, replies)
    case h <> t:
      Asking{h <> t, [], names}

# the upgrade's questions first, since the packages the lock reads depend on
# where the pins move
def step.ups(
  ups: List<&2, Up.Ask>,
  +here: String,
  +nx: Up.Next,
  +listing: W.Listing,
  +replies: List<&2, W.Reply>
) -> Step:
  match ups:
    case []:
      step.pkgs(wants.of(here, nx, listing, replies), names.wants.of(nx, listing, replies), nx,
        listing, replies)
    case h <> t:
      Asking{[], queries(here, h <> t), []}

# what the interpreter does next on a World. The upgrade is decided once per
# round, and every answer of the round is read from that one decision.
def step(world: W.World) -> Step:
  W.World{+args, +ledger, +listing, +replies, ups} = world
  +nx = W.next(args, ledger, ups)
  step.ups(Up.next.asks(nx), W.here.of(args), nx, listing, replies)
