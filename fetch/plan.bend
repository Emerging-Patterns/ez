# fetch/plan: `ez fetch` as a pure planner. It reads a World
# (fetch/world.bend) and returns either the questions it still needs
# answered (`step`) or a Plan: the effects to run and how the command ends
# (`plan`). The interpreter (fetch/run.bend) loops on `step`, answering each
# question by IO, until nothing is left to ask, then executes the plan.
#
# `ez fetch` fills BEND_LIB from the lock alone, re-resolving nothing. With no
# ez.toml, or no ez.lock.toml, it refuses before it asks anything, as
# `uv sync --frozen` does: a fetch never writes a lock, so it has nothing to
# fill BEND_LIB from.
#
# For every package the lock records it asks first for the tree already under
# BEND_LIB. A tree there that the lock's checks pass is kept as it is. Any
# other is fetched: a git package as a shallow checkout at the pinned rev,
# from its source anchored at the project (`P.anchor(here, url)`), and a hub
# package from the lock's hub. Each file is then taken from what arrived by
# its path, from the package's root inside the checkout for a git package,
# and the package is checked before anything is laid (`good`): every file's
# digest equals the sum the lock records for it (EZ-FETCH-1), no path leaves
# the package, and the files hash to the name the lock records them under
# (EZ-HASH-3). A git package's checkout must also weigh to the narHash the
# lock records (`weighed`), so the files laid come from the tree the lock
# pins, the tree nix rebuilds from the same pin. Only then is the tree laid
# under BEND_LIB, the files the lock names and their manifest last.
#
# Every name the lock records is laid too, as the file bend reads the name's
# hash from, `$BEND_LIB/names/<nv>` holding the hash and a newline, so bend
# never asks the hub for it (EZ-HUB-4). A names file that already holds the
# lock's hash is kept; any other is written, and one that held another hash
# is said to have been rewritten, since the lock wins over it as it wins over
# a tree that fails its checks. A name the lock records that bend would not
# read back, one the hub rules out or a hash that is not a `0x` name, refuses
# the fetch, since its file would not be the one bend reads.
#
# The plan of a fetch that succeeds lays every tree that was fetched and every
# names file that is not already right, and nothing else: no ledger, no lock. A fetch that refuses, for any package,
# has no effect at all, so a package fetched before the one that failed is
# not laid either, and a tree already under BEND_LIB is never removed
# (EZ-OUT-2).
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), as for
# `ez add`, `ez remove` and `ez init`.
import Base
import ../toml/toml.bend as T
import ./world.bend as F
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/up.bend as Up
import ../lock/lock.bend as L
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../sha/sha.bend as Sha

# ---------------------------------------------------------------------------
# the questions

# the question that fetches a package from where the lock says it comes from:
# a checkout of a git package at its rev, from its source as git is to read
# it, a relative path taken from the project; or a hub package from the hub
def fetch.ask(src: L.Src, +here: String, +hub: String, +hash: String) -> F.Ask:
  match src:
    case L.Hub{}:
      F.Hub{W.Pkg{hash, L.Hub{}, hub}}
    case L.Git{url, rev, _entry, _root, _nar, _tag}:
      F.Git{hash, Up.Clone{Path.anchor(here, url), rev}}

# ---------------------------------------------------------------------------
# what arrived

# a package's files as they arrived, with the directory the lock's paths are
# written from inside them, or why nothing arrived
type Tree is Data:
  Tree{root: String, files: List<&2, K.Source>}
  Gone{why: String}

# the files a manifest names, each with the text read for it
def zip(fs: List<&2, K.File>, ss: List<&2, String>) -> List<&2, K.Source>:
  match fs ss:
    case Nil{} Nil{}:
      []
    case Nil{} Con{_s, _t}:
      []
    case Con{_f, _g} Nil{}:
      []
    case Con{f, g} Con{s, t}:
      K.Source{K.file.at(f), s} <> zip(g, t)

# a manifest and the texts of the files it names, as a tree: what is under
# BEND_LIB, or what the hub served
def tree.read(answer: W.Answer) -> Tree:
  match answer:
    case W.Got{_how, manifest, ss}:
      Tree{"", zip(L.manifest.files(String.lines(manifest)), ss)}
    case W.Miss{why}:
      Gone{why}
    case _:
      Gone{"ez: a tree was not answered with one"}

# a checkout at the pinned rev, whose paths are the lock's from `root`
def tree.said(answer: Up.Answer, +root: String) -> Tree:
  match answer:
    case Up.Cloned{_nar, fs}:
      Tree{root, fs}
    case Up.Miss{why}:
      Gone{why}
    case _:
      Gone{"ez: a checkout was not answered with one"}

# what arrived for a question
def tree.of(answer: F.Answer, +root: String) -> Tree:
  match answer:
    case F.Read{a}:
      tree.read(a)
    case F.Said{a}:
      tree.said(a, root)
    case F.Held{_got}:
      Gone{"ez: a tree was not answered with one"}

# a text looked up, "" when it is not there
def text.or(got: Maybe<&2, String>) -> String:
  match got:
    case None{}:
      ""
    case Some{text}:
      text

# where a path of the lock is in a tree: under its root inside a checkout,
# and as it is in a tree a manifest names
def key(+root: String, +at: String) -> String:
  Bool.pick(String, String.is_empty(root), at, Path.join(root, at))

# every file the lock names, with the text the tree has at its path. A file
# the tree does not have is taken as empty, which does not match the lock
# unless the lock records an empty file.
def cand(fs: List<&2, K.File>, +root: String, +tree: List<&2, K.Source>) -> List<&2, W.Source>:
  match fs:
    case []:
      []
    case K.File{+at, _sum} <> t:
      W.Source{at, text.or(K.look(tree, key(root, at)))} <> cand(t, root, tree)

# ---------------------------------------------------------------------------
# the checks

# a file laid, weighed by its own text
def weigh(src: W.Source) -> K.File:
  W.Source{at, +text} = src
  K.File{at, Sha.hex(text)}

# every file laid, weighed by its own text
def weighs(ls: List<&2, W.Source>) -> List<&2, K.File>:
  match ls:
    case []:
      []
    case h <> t:
      weigh(h) <> weighs(t)

# whether one file is the one the lock names: the same path, and a text whose
# digest is the sum the lock records
def fit(want: K.File, got: W.Source) -> Bool:
  K.File{+at, sum} = want
  W.Source{lat, +text} = got
  Bool.and(String.eq(lat, at), String.eq(Sha.hex(text), sum))

# whether every file is the one the lock names, in the lock's order. A list
# longer or shorter than the lock's is not the package.
def fits(fs: List<&2, K.File>, ls: List<&2, W.Source>) -> Bool:
  match fs ls:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{_l, _m}:
      False{}
    case Con{_f, _g} Nil{}:
      False{}
    case Con{f, g} Con{l, m}:
      +rest = fits(g, m)
      Bool.and(fit(f, l), rest)

# whether a path stays inside the tree it is laid in: written the way the
# path walk writes it, so no `.` or `//` in it, not empty, not absolute and
# not climbing out with `..`. A lock is not trusted with where it writes.
def path.safe(+at: String) -> Bool:
  Bool.and(String.eq(Path.norm(at), at),
    Bool.not(Bool.or(K.escapes(at), String.eq(at, "."))))

# whether every path stays inside the tree
def paths.safe(ls: List<&2, W.Source>) -> Bool:
  match ls:
    case []:
      True{}
    case W.Source{+at, _text} <> t:
      +rest = paths.safe(t)
      Bool.and(path.safe(at), rest)

# the manifest of the files laid, weighed by their own texts
def manifest(+ls: List<&2, W.Source>) -> String:
  K.manifest_of(K.files_of(weighs(ls)))

# the `0x` name of the files laid, weighed by their own texts
def named(+ls: List<&2, W.Source>) -> String:
  K.hash_of(K.files_of(weighs(ls)))

# whether a package may be laid: every file is the one the lock names, no
# path leaves the tree, and the files hash to the name the lock records them
# under, so the tree laid under that name is that name's
def good(fs: List<&2, K.File>, +hash: String, +ls: List<&2, W.Source>) -> Bool:
  +fit = fits(fs, ls)
  +safe = paths.safe(ls)
  Bool.and(fit, Bool.and(safe, String.eq(hash, named(ls))))

# the first file that is not the one the lock names, or "" when none is
# wrong. A path is never empty, so "" is never such a path.
def unfit.pick(ok: Bool, +at: String, rest: String) -> String:
  match ok:
    case True{}:
      rest
    case False{}:
      at

# the first path that does not fit, "" when every file does
def unfit(fs: List<&2, K.File>, ls: List<&2, W.Source>) -> String:
  match fs ls:
    case Nil{} Nil{}:
      ""
    case Nil{} Con{l, _m}:
      W.Source{at, _text} = l
      at
    case Con{f, _g} Nil{}:
      K.file.at(f)
    case Con{+f, g} Con{l, m}:
      unfit.pick(fit(f, l), K.file.at(f), unfit(g, m))

# why a package may not be laid, naming it
def bad.why(fs: List<&2, K.File>, +hash: String, +ls: List<&2, W.Source>) -> String:
  +at = unfit(fs, ls)
  Bool.pick(String, String.is_empty(at),
    Bool.pick(String, paths.safe(ls),
      "ez: " ++ hash ++ ": its files do not hash to its name",
      "ez: " ++ hash ++ ": a path in the lock leaves the package"),
    "ez: " ++ hash ++ ": " ++ at ++ " does not match the lock")

# ---------------------------------------------------------------------------
# one package

# where one package stands: its tree under BEND_LIB still to read, its fetch
# still to ask, a tree under BEND_LIB that passed and is kept, the files that
# arrived, or why nothing arrived
type Part is Data:
  AskLaid{}
  AskFetch{}
  Have{}
  Got{files: List<&2, W.Source>}
  No{why: String}

# the files that arrived for a package, or why none did
def part.tree(tree: Tree, fs: List<&2, K.File>) -> Part:
  match tree:
    case Tree{r, files}:
      Got{cand(fs, r, files)}
    case Gone{why}:
      No{why}

# a package fetched, once it is answered
def part.fetch.heard(got: F.Heard, fs: List<&2, K.File>, +root: String) -> Part:
  match got:
    case F.Open{}:
      AskFetch{}
    case F.Heard{answer}:
      part.tree(tree.of(answer, root), fs)

# a package fetched, from where the lock says it comes from
def part.fetch(
  +rs: List<&2, F.Reply>,
  +src: L.Src,
  fs: List<&2, K.File>,
  +here: String,
  +hub: String,
  +hash: String
) -> Part:
  part.fetch.heard(F.heard(rs, fetch.ask(src, here, hub, hash)), fs, L.src.root(src))

# a tree under BEND_LIB that passes is kept; any other is fetched
def part.kept(
  ok: Bool,
  +rs: List<&2, F.Reply>,
  +src: L.Src,
  fs: List<&2, K.File>,
  +here: String,
  +hub: String,
  +hash: String
) -> Part:
  match ok:
    case True{}:
      Have{}
    case False{}:
      part.fetch(rs, src, fs, here, hub, hash)

# the tree under BEND_LIB, read: checked the way a fetched one is, and
# fetched when it is not there
def part.found(
  tree: Tree,
  +rs: List<&2, F.Reply>,
  +src: L.Src,
  +fs: List<&2, K.File>,
  +here: String,
  +hub: String,
  +hash: String
) -> Part:
  match tree:
    case Tree{_r, files}:
      part.kept(good(fs, hash, cand(fs, "", files)), rs, src, fs, here, hub, hash)
    case Gone{_why}:
      part.fetch(rs, src, fs, here, hub, hash)

# the tree under BEND_LIB, once it is read
def part.laid(
  got: F.Heard,
  +rs: List<&2, F.Reply>,
  +src: L.Src,
  +fs: List<&2, K.File>,
  +here: String,
  +hub: String,
  +hash: String
) -> Part:
  match got:
    case F.Open{}:
      AskLaid{}
    case F.Heard{answer}:
      part.found(tree.of(answer, ""), rs, src, fs, here, hub, hash)

# where one package stands
def part(
  +rs: List<&2, F.Reply>,
  +src: L.Src,
  +fs: List<&2, K.File>,
  +here: String,
  +hub: String,
  +hash: String
) -> Part:
  part.laid(F.heard(rs, F.Laid{hash}), rs, src, fs, here, hub, hash)

# ---------------------------------------------------------------------------
# the checkout around a git package

# why a checkout may not be laid for the narHash it weighed to, "" when it
# may: the lock records a narHash and the checkout weighed to it
def nar.why(
  none: Bool,
  same: Bool,
  +hash: String,
  +want: String,
  +got: String,
  +url: String,
  +rev: String
) -> String:
  match none:
    case True{}:
      "ez: " ++ hash ++ ": the lock records no narHash for " ++ url ++ " at " ++ rev ++
        ", so its checkout cannot be checked; run `ez lock --upgrade` to pin it"
    case False{}:
      match same:
        case True{}:
          ""
        case False{}:
          "ez: " ++ hash ++ ": " ++ url ++ " at " ++ rev ++ " has narHash " ++ got ++
            ", and the lock records " ++ want

# why a package stands without a weighed checkout
def unweighed(+hash: String) -> String:
  "ez: " ++ hash ++ ": its checkout was not weighed"

# what a checkout question was answered with, against the lock's narHash
def weighed.up(answer: Up.Answer, +hash: String, +nar: String, +url: String, +rev: String) -> String:
  match answer:
    case Up.Cloned{+got, _fs}:
      nar.why(String.is_empty(nar), String.eq(got, nar), hash, nar, got, url, rev)
    case _:
      unweighed(hash)

def weighed.answer(answer: F.Answer, +hash: String, +nar: String, +url: String, +rev: String) -> String:
  match answer:
    case F.Said{a}:
      weighed.up(a, hash, nar, url, rev)
    case F.Read{_a}:
      unweighed(hash)
    case F.Held{_got}:
      unweighed(hash)

def weighed.heard(got: F.Heard, +hash: String, +nar: String, +url: String, +rev: String) -> String:
  match got:
    case F.Heard{a}:
      weighed.answer(a, hash, nar, url, rev)
    case F.Open{}:
      unweighed(hash)

def weighed.src(src: L.Src, +rs: List<&2, F.Reply>, +here: String, +hash: String) -> String:
  match src:
    case L.Hub{}:
      ""
    case L.Git{+url, +rev, _entry, _root, nar, _tag}:
      weighed.heard(F.heard(rs, F.Git{hash, Up.Clone{Path.anchor(here, url), rev}}),
        hash, nar, url, rev)

# why the checkout a package of the lock was fetched as may not be laid, ""
# when it may. A hub package has no checkout. A git package's checkout, the
# one its fetch question was answered with, must weigh to the narHash the
# lock records, so what is laid comes from the tree the lock pins and not
# only from files that happen to match their sums.
def weighed(+ss: List<&2, T.Sect>, +rs: List<&2, F.Reply>, +here: String, +hash: String) -> String:
  weighed.src(L.pack.src(L.pack_of(ss, hash)), rs, here, hash)

def weigh.got(ok: Bool, +why: String, ls: List<&2, W.Source>) -> Part:
  match ok:
    case True{}:
      Got{ls}
    case False{}:
      No{why}

# files that arrived stand only when the checkout they came from weighed to
# the lock's narHash. A tree kept from BEND_LIB was not fetched, and is
# checked file by file as before.
def weigh.part(+why: String, part: Part) -> Part:
  match part:
    case AskLaid{}:
      AskLaid{}
    case AskFetch{}:
      AskFetch{}
    case Have{}:
      Have{}
    case Got{ls}:
      weigh.got(String.is_empty(why), why, ls)
    case No{w}:
      No{w}

# one package of the lock, and where it stands
type Pt is Data:
  Pt{hash: String, src: L.Src, files: List<&2, K.File>, part: Part}

# every package of the lock, and where each stands
def parts(
  +ss: List<&2, T.Sect>,
  +rs: List<&2, F.Reply>,
  +here: String,
  +hub: String,
  hs: List<&2, String>
) -> List<&2, Pt>:
  match hs:
    case []:
      []
    case +h <> t:
      +pk = L.pack_of(ss, h)
      +src = L.pack.src(pk)
      +fs = L.pack.files(pk)
      Pt{h, src, fs, weigh.part(weighed(ss, rs, here, h), part(rs, src, fs, here, hub, h))}
        <> parts(ss, rs, here, hub, t)

# ---------------------------------------------------------------------------
# the names

# where one name of the lock stands: its names file still to read, a file
# that already holds the lock's hash, a file to write, with the hash the one
# there held ("" when there was none), or why the name refuses the fetch
type Nm is Data:
  NmAsk{nv: String}
  NmKeep{}
  NmPut{nv: String, hash: String, was: String}
  NmStop{why: String}

# a names file that was there, against the lock's hash. bend trims the file
# before it reads the hash, and so does this.
def name.held(same: Bool, +nv: String, +hash: String, +was: String) -> Nm:
  match same:
    case True{}:
      NmKeep{}
    case False{}:
      NmPut{nv, hash, was}

# what BEND_LIB holds for a name
def name.got(got: Maybe<&2, String>, +nv: String, +hash: String) -> Nm:
  match got:
    case None{}:
      NmPut{nv, hash, ""}
    case Some{text}:
      +was = String.trim(text)
      name.held(String.eq(was, hash), nv, hash, was)

# a names file, once it is read
def name.answer(answer: F.Answer, +nv: String, +hash: String) -> Nm:
  match answer:
    case F.Held{got}:
      name.got(got, nv, hash)
    case _:
      NmStop{"ez: " ++ nv ++ ": its names file was not read"}

def name.heard(got: F.Heard, +nv: String, +hash: String) -> Nm:
  match got:
    case F.Open{}:
      NmAsk{nv}
    case F.Heard{a}:
      name.answer(a, nv, hash)

# a name bend would read back is looked for under BEND_LIB; any other stops
# the fetch, since the file laid for it would not be the one bend reads
def name.valid(ok: Bool, +rs: List<&2, F.Reply>, +nv: String, +hash: String) -> Nm:
  match ok:
    case True{}:
      name.heard(F.heard(rs, F.Named{nv}), nv, hash)
    case False{}:
      NmStop{"ez: the lock names " ++ nv ++ " as " ++ hash ++
        ", which bend would not read back; run ez lock"}

# where one name of the lock stands
def name.part(+rs: List<&2, F.Reply>, name: L.Name) -> Nm:
  L.Name{+nv, +hash} = name
  name.valid(L.name.valid(L.Name{nv, hash}), rs, nv, hash)

# where every name of the lock stands
def name.parts(+rs: List<&2, F.Reply>, ns: List<&2, L.Name>) -> List<&2, Nm>:
  match ns:
    case []:
      []
    case h <> t:
      name.part(rs, h) <> name.parts(rs, t)

# how a rewritten names file is said to have been rewritten
def name.rewrote(+nv: String, +hash: String, +was: String) -> String:
  "ez: BEND_LIB/names/" ++ nv ++ " named " ++ was ++ ", and the lock names " ++ hash ++
    "; rewrote it"

# a names file written, said first when it held another hash
def name.put.at(none: Bool, +nv: String, +hash: String, was: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match none:
    case True{}:
      P.Name{nv, hash} <> rest
    case False{}:
      P.Say{name.rewrote(nv, hash, was)} <> P.Name{nv, hash} <> rest

def name.put(+nv: String, +hash: String, +was: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  name.put.at(String.is_empty(was), nv, hash, was, rest)

# every names file a fetch writes, ahead of what follows
def names.lay(ms: List<&2, Nm>, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match ms:
    case []:
      rest
    case m <> t:
      match m:
        case NmPut{nv, hash, was}:
          name.put(nv, hash, was, names.lay(t, rest))
        case _:
          names.lay(t, rest)

# how the names end the fetch: the first that refuses, or `o`, how the
# packages ended it, which comes first
def names.outcome(ms: List<&2, Nm>) -> P.Outcome:
  match ms:
    case []:
      P.Success{}
    case m <> t:
      match m:
        case NmStop{why}:
          P.Refused{why}
        case NmAsk{nv}:
          P.Refused{"ez: " ++ nv ++ " was never looked for under BEND_LIB"}
        case _:
          names.outcome(t)

# the packages' end, or, when they succeed, the names'
def outcome.then(first: P.Outcome, then: P.Outcome) -> P.Outcome:
  match first:
    case P.Success{}:
      then
    case P.Refused{why}:
      P.Refused{why}

# the names still to read under BEND_LIB
def names.asks(ms: List<&2, Nm>) -> List<&2, F.Ask>:
  match ms:
    case []:
      []
    case m <> t:
      match m:
        case NmAsk{nv}:
          F.Named{nv} <> names.asks(t)
        case _:
          names.asks(t)

# every name the lock records, and where each stands
def name.parts.of(+ss: List<&2, T.Sect>, +world: F.World) -> List<&2, Nm>:
  name.parts(F.replies(world), L.names(ss))

# ---------------------------------------------------------------------------
# the verdict

# what one package comes to: nothing to do, a tree to lay, or a refusal
type Verdict is Data:
  Keep{}
  Put{hash: String, files: List<&2, W.Source>}
  Stop{why: String}

# the files that arrived, laid when they pass
def judge.got(ok: Bool, fs: List<&2, K.File>, +hash: String, +ls: List<&2, W.Source>) -> Verdict:
  match ok:
    case True{}:
      Put{hash, ls}
    case False{}:
      Stop{bad.why(fs, hash, ls)}

# what one package comes to, where it stands
def judge(+fs: List<&2, K.File>, +hash: String, part: Part) -> Verdict:
  match part:
    case AskLaid{}:
      Stop{"ez: " ++ hash ++ " was never looked for under BEND_LIB"}
    case AskFetch{}:
      Stop{"ez: " ++ hash ++ " was never fetched"}
    case Have{}:
      Keep{}
    case Got{+ls}:
      judge.got(good(fs, hash, ls), fs, hash, ls)
    case No{why}:
      Stop{why}

# what every package comes to
def judged(ps: List<&2, Pt>) -> List<&2, Verdict>:
  match ps:
    case []:
      []
    case Pt{h, _src, fs, p} <> t:
      judge(fs, h, p) <> judged(t)

# a tree laid under BEND_LIB: the files the lock names, then their manifest,
# so a tree that has one is a tree that finished
def lay(+hash: String, +ls: List<&2, W.Source>) -> P.Effect:
  P.Lay{P.Cache{}, hash, List.append(&2, W.Source, ls, [W.Source{"manifest", manifest(ls)}])}

# one verdict's effect, ahead of the rest
def effect.v(verdict: Verdict, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match verdict:
    case Keep{}:
      rest
    case Put{hash, ls}:
      lay(hash, ls) <> rest
    case Stop{_why}:
      rest

# every verdict's effect
def effects.of(vs: List<&2, Verdict>) -> List<&2, P.Effect>:
  match vs:
    case []:
      []
    case v <> t:
      effect.v(v, effects.of(t))

# how the command ends: the first refusal, or success
def outcome.of(vs: List<&2, Verdict>) -> P.Outcome:
  match vs:
    case []:
      P.Success{}
    case v <> t:
      match v:
        case Stop{why}:
          P.Refused{why}
        case _:
          outcome.of(t)

# a plan that refuses has no effect at all; its reason is how it ends
def seal(es: List<&2, P.Effect>, outcome: P.Outcome) -> P.Plan:
  match outcome:
    case P.Success{}:
      P.Plan{es, P.Success{}}
    case P.Refused{why}:
      P.Plan{[], P.Refused{why}}

# the plan once every package and every name stands somewhere: the names
# files, then the trees, and how the command ends. Each verdict is made once
# and read by both halves.
def plan.parts(ps: List<&2, Pt>, +ms: List<&2, Nm>) -> P.Plan:
  +vs = judged(ps)
  seal(names.lay(ms, effects.of(vs)), outcome.then(outcome.of(vs), names.outcome(ms)))

# ---------------------------------------------------------------------------
# the plan

# every package of the lock on a World that has one, and where each stands
def parts.of(+ss: List<&2, T.Sect>, +world: F.World) -> List<&2, Pt>:
  parts(ss, F.replies(world), F.here(world), L.lock.hub(ss), L.hashes(ss))

# why a fetch refuses before anything is asked: no ez.toml, or no lock
def need.no() -> String:
  "ez: no " ++ F.toml() ++ " here; ez fetch fills BEND_LIB for a project's lock, " ++
    "and ez init makes one"

def need.lock() -> String:
  "ez: no " ++ F.lockfile() ++ " here; ez fetch reads the lock and resolves " ++
    "nothing, and ez lock writes it"

# the plan once the ledger and the lock are known to be there
def plan.lock(got: Maybe<&2, String>, +world: F.World) -> P.Plan:
  match got:
    case None{}:
      P.Plan{[], P.Refused{need.lock()}}
    case Some{_text}:
      +ss = F.sects(world)
      plan.parts(parts.of(ss, world), name.parts.of(ss, world))

# the plan: a missing ledger, then a missing lock, refused before the rest
def plan.led(led: Bool, got: Maybe<&2, String>, +world: F.World) -> P.Plan:
  match led:
    case False{}:
      P.Plan{[], P.Refused{need.no()}}
    case True{}:
      plan.lock(got, world)

# `ez fetch` over a World
def plan(+world: F.World) -> P.Plan:
  plan.led(F.ledger(world), F.lock(world), world)

# whether a plan ends in a refusal
def refuses.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether `ez fetch` refuses on a World
def refuses(+world: F.World) -> Bool:
  refuses.plan(plan(world))

# ---------------------------------------------------------------------------
# what is still to ask

# one package's open question, ahead of the rest
def ask.pt(pt: Pt, +here: String, +hub: String, rest: List<&2, F.Ask>) -> List<&2, F.Ask>:
  Pt{+h, src, _fs, p} = pt
  match p:
    case AskLaid{}:
      F.Laid{h} <> rest
    case AskFetch{}:
      fetch.ask(src, here, hub, h) <> rest
    case _:
      rest

# every open question
def asks.of(ps: List<&2, Pt>, +here: String, +hub: String) -> List<&2, F.Ask>:
  match ps:
    case []:
      []
    case p <> t:
      ask.pt(p, here, hub, asks.of(t, here, hub))

# the open questions once the ledger and the lock are known to be there
def wants.lock(got: Maybe<&2, String>, +world: F.World) -> List<&2, F.Ask>:
  match got:
    case None{}:
      []
    case Some{_text}:
      +ss = F.sects(world)
      List.append(&2, F.Ask, asks.of(parts.of(ss, world), F.here(world), L.lock.hub(ss)),
        names.asks(name.parts.of(ss, world)))

def wants.led(led: Bool, got: Maybe<&2, String>, +world: F.World) -> List<&2, F.Ask>:
  match led:
    case False{}:
      []
    case True{}:
      wants.lock(got, world)

# the questions a World still leaves open: none when the fetch refuses before
# it asks, and otherwise one for each package that does not yet stand
# anywhere
def wants(+world: F.World) -> List<&2, F.Ask>:
  wants.led(F.ledger(world), F.lock(world), world)

# the questions still open, or the plan once there are none
type Step is Data:
  Asking{asks: List<&2, F.Ask>}
  Run{plan: P.Plan}

def step.asks(asks: List<&2, F.Ask>, ps: List<&2, Pt>, ms: List<&2, Nm>) -> Step:
  match asks:
    case []:
      Run{plan.parts(ps, ms)}
    case h <> t:
      Asking{h <> t}

def step.lock(got: Maybe<&2, String>, +world: F.World) -> Step:
  match got:
    case None{}:
      Run{P.Plan{[], P.Refused{need.lock()}}}
    case Some{_text}:
      +ss = F.sects(world)
      +ps = parts.of(ss, world)
      +ms = name.parts.of(ss, world)
      step.asks(List.append(&2, F.Ask, asks.of(ps, F.here(world), L.lock.hub(ss)), names.asks(ms)),
        ps, ms)

def step.led(led: Bool, got: Maybe<&2, String>, +world: F.World) -> Step:
  match led:
    case False{}:
      Run{P.Plan{[], P.Refused{need.no()}}}
    case True{}:
      step.lock(got, world)

# what the interpreter does next on a World. Every package is placed once per
# round, and both the questions and the plan are read from that.
def step(+world: F.World) -> Step:
  step.led(F.ledger(world), F.lock(world), world)

# ---------------------------------------------------------------------------
# law vocabulary

# the effects of a plan
def effects(pl: P.Plan) -> List<&2, P.Effect>:
  P.Plan{es, _outcome} = pl
  es

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

# the files the lock records under a hash
def locked(+ss: List<&2, T.Sect>, +hash: String) -> List<&2, K.File>:
  L.pack.files(L.pack_of(ss, hash))

# whether an effect that lays a tree lays the files the lock records under
# its hash, each with a text whose digest is the lock's sum for it
def lays.one(+ss: List<&2, T.Sect>, effect: P.Effect) -> Bool:
  match effect:
    case P.Lay{_place, hash, fs}:
      fits(locked(ss, hash), front(fs))
    case _:
      True{}

# whether every tree a list of effects lays is the one the lock records
def lays.locked(+ss: List<&2, T.Sect>, es: List<&2, P.Effect>) -> Bool:
  match es:
    case []:
      True{}
    case h <> t:
      +rest = lays.locked(ss, t)
      Bool.and(lays.one(ss, h), rest)

# the source a checkout is asked of, "" for any other question
def clone.url(ask: Up.Ask) -> String:
  match ask:
    case Up.Clone{url, _rev}:
      url
    case _:
      ""

# the package a question is about
def ask.hash(ask: F.Ask) -> String:
  match ask:
    case F.Laid{hash}:
      hash
    case F.Git{hash, _q}:
      hash
    case F.Hub{q}:
      W.ask.hash(q)
    case F.Named{nv}:
      nv

# whether a git question asks for the source the lock records for its
# package, taken from the project: the lock's url anchored at `here`
def ask.anchored(+here: String, src: L.Src, ask: F.Ask) -> Bool:
  match ask:
    case F.Git{_hash, q}:
      String.eq(clone.url(q), Path.anchor(here, L.src.url(src)))
    case _:
      True{}

# whether every question does
def asks.anchored(+here: String, +ss: List<&2, T.Sect>, as: List<&2, F.Ask>) -> Bool:
  match as:
    case []:
      True{}
    case +h <> t:
      +rest = asks.anchored(here, ss, t)
      Bool.and(ask.anchored(here, L.pack.src(L.pack_of(ss, ask.hash(h))), h), rest)

# whether an effect that lays a tree lays a package whose checkout, when it
# has one, weighed to the narHash the lock records
def weighed.lay(
  +ss: List<&2, T.Sect>,
  +rs: List<&2, F.Reply>,
  +here: String,
  effect: P.Effect
) -> Bool:
  match effect:
    case P.Lay{_place, hash, _fs}:
      String.is_empty(weighed(ss, rs, here, hash))
    case _:
      True{}

# whether every tree a list of effects lays does
def lays.weighed(
  +ss: List<&2, T.Sect>,
  +rs: List<&2, F.Reply>,
  +here: String,
  es: List<&2, P.Effect>
) -> Bool:
  match es:
    case []:
      True{}
    case h <> t:
      +rest = lays.weighed(ss, rs, here, t)
      Bool.and(weighed.lay(ss, rs, here, h), rest)
