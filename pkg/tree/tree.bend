# pkg/tree: a spike of the package walk made pure, for the design in
# docs/rfc/ez-add-planner.md. Nothing imports this module: `ez add` still
# runs `K.pkg_of`, which reads the checkout from disk, and this file changes
# none of its behavior. It exists to show that the walk can be a total pure
# function of a checkout's files, which is what `ez add` in planner form needs
# to make EZ-RES-2 and EZ-HASH-3 statements about its plan.
#
# The walk is `K.pkg_of`'s, step for step: the same scan, the same queue, the
# same names. Three things differ. A file is looked up in the checkout's file
# list instead of read. A module that climbs out of the entry's directory
# re-roots the package under the entry's own trailing components, which the
# checkout-relative entry path already holds, instead of asking `realpath`.
# And the walk keeps each file's text beside its name, so the plan can lay
# the very bytes it hashed.
import Base
import ../pkg.bend as K
import ../path.bend as P
import ../../sha/sha.bend as Sha

# one file of a checkout: its path from the checkout's top, and its text
type Source is Data:
  Source{at: String, text: String}

# a file of the package as the walk found it: the name it takes inside the
# package, and its text
type Found is Data:
  Found{raw: String, text: String}

# the walk so far: the files already visited, what was found, the first
# file that was imported and is not in the checkout ("" while there is none),
# and the files still to visit
type State is Data:
  State{seen: List<&2, String>, out: List<&2, Found>, miss: String, queue: List<&2, K.Task>}

# what the walk made of a checkout: the package, or why there is none
type Walked is Data:
  Walked{hash: String, root: String, files: List<&2, Source>}
  Refused{why: String}

# one step of a lookup, with the head's answer in hand. The rest arrives as a
# thunk, so a hit ends the search.
def look.step(hit: Bool, text: String, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{text}
    case False{}:
      rest(Unit{})

# a checkout's text for a path, first in the list, or None when it has none
def look(fs: List<&2, Source>, +at: String) -> Maybe<&2, String>:
  match fs:
    case []:
      None{}
    case Source{+h, text} <> t:
      look.step(String.eq(h, at), text, _u => look(t, at))

# one foreign body, or nothing when the checkout does not hold it. bend
# uploads only the ones that are there.
def foreign.put(got: Maybe<&2, String>, +raw: String) -> List<&2, Found>:
  match got:
    case None{}:
      []
    case Some{text}:
      [Found{raw, text}]

# every foreign body a file imports, named from the importing module's
# directory, as `K.foreigns` names them
def foreigns(+fs: List<&2, Source>, +dir: String, +nd: String, ats: List<&2, String>) -> List<&2, Found>:
  match ats:
    case []:
      []
    case +h <> t:
      List.append(&2, Found, foreign.put(look(fs, P.join(dir, h)), P.join(nd, h)),
        foreigns(fs, dir, nd, t))

# a file that is in the checkout: itself and its foreign bodies found, and
# the modules it imports put at the front of the queue, so the walk goes depth
# first the way bend's does
def visit.found(
  +fs: List<&2, Source>,
  +text: String,
  +file: String,
  +ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Found>,
  miss: String,
  rest: List<&2, K.Task>
) -> State:
  +sc = K.scan(text)
  +d = P.dir(file)
  +nd = K.nsdir(ns)
  State{file <> seen,
    Found{K.raw_of(ns, eb), text} <> List.append(&2, Found,
      foreigns(fs, d, nd, K.scan.foreign(sc)), out),
    miss,
    List.append(&2, K.Task, K.tasks(d, nd, K.scan.mods(sc)), rest)}

# a module that is imported and not in the checkout stops the walk, since a
# package missing a file is not the package bend would publish
def visit.have(
  got: Maybe<&2, String>,
  +fs: List<&2, Source>,
  +file: String,
  ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Found>,
  miss: String,
  rest: List<&2, K.Task>
) -> State:
  match got:
    case None{}:
      State{seen, out, file, rest}
    case Some{text}:
      visit.found(fs, text, file, ns, eb, seen, out, miss, rest)

# a file already visited keeps the name it was first reached through, the way
# bend's own walk does
def visit.go(
  hit: Bool,
  +fs: List<&2, Source>,
  +file: String,
  ns: String,
  eb: String,
  seen: List<&2, String>,
  out: List<&2, Found>,
  miss: String,
  rest: List<&2, K.Task>
) -> State:
  match hit:
    case True{}:
      State{seen, out, miss, rest}
    case False{}:
      visit.have(look(fs, file), fs, file, ns, eb, seen, out, miss, rest)

# the next file of the queue visited, or the walk as it is when the queue is
# empty
def step.pop(
  +fs: List<&2, Source>,
  eb: String,
  +seen: List<&2, String>,
  out: List<&2, Found>,
  miss: String,
  queue: List<&2, K.Task>
) -> State:
  match queue:
    case []:
      State{seen, out, miss, []}
    case K.Task{+file, ns} <> t:
      visit.go(K.seen.has(seen, file), fs, file, ns, eb, seen, out, miss, t)

# the walk as one step that does not recurse
def step(+fs: List<&2, Source>, eb: String, st: State) -> State:
  State{seen, out, miss, queue} = st
  step.pop(fs, eb, seen, out, miss, queue)

# whether the walk is over: its queue is empty, or it stopped on a missing file
def walk.done(+st: State) -> Bool:
  State{_seen, _out, +miss, queue} = st
  Bool.or(List.is_empty(&2, K.Task, queue), Bool.not(String.is_empty(miss)))

# the walk as it is when it is over, or one step further when it is not. The
# rest of the walk arrives as a function, since a def may not call itself from
# another def.
def walk.more(done: Bool, st: State, go: State -> State) -> State:
  match done:
    case True{}:
      st
    case False{}:
      go(st)

# the fuel ran out with files still queued: stopped on the first of them, so
# it is refused rather than hashed short
def walk.spent(st: State) -> State:
  State{seen, out, miss, queue} = st
  match queue:
    case []:
      State{seen, out, miss, []}
    case K.Task{+file, ns} <> t:
      State{seen, out, file, K.Task{file, ns} <> t}

# every file of the package, reached from the entry, the step iterated under
# fuel
def walk(fuel: Nat, +fs: List<&2, Source>, +eb: String, +st: State) -> State:
  match fuel:
    case 0n:
      walk.spent(st)
    case 1n+f:
      walk.more(walk.done(st), st, now => walk(f, fs, eb, step(fs, eb, now)))

# ---------------------------------------------------------------------------
# the package

# a found file as `K.pkg_of` records it: its name and the sha256 of its text
def found.sum(hit: Found) -> K.Found:
  Found{raw, +text} = hit
  K.Found{raw, Sha.hex(text)}

# every found file with its sum
def found.sums(fs: List<&2, Found>) -> List<&2, K.Found>:
  match fs:
    case []:
      []
    case h <> t:
      found.sum(h) <> found.sums(t)

# a found file placed under whatever the package re-rooted at, with its text
def laid.one(+pre: String, hit: Found) -> Source:
  Found{raw, text} = hit
  Source{P.join(pre, raw), text}

# every found file placed, with its text
def laid(+pre: String, fs: List<&2, Found>) -> List<&2, Source>:
  match fs:
    case []:
      []
    case h <> t:
      laid.one(pre, h) <> laid(pre, t)

# a laid file weighed: its path and the sha256 of its text. This is what a
# plan's reader would compute from the files a `Lay` writes.
def sum(src: Source) -> K.File:
  Source{at, +text} = src
  K.File{at, Sha.hex(text)}

# every laid file weighed
def sums(fs: List<&2, Source>) -> List<&2, K.File>:
  match fs:
    case []:
      []
    case h <> t:
      sum(h) <> sums(t)

# the found files named and weighed, once no path escapes the package
def made.judge(ok: Bool, +bad: String, +root: String, +pre: String, +out: List<&2, Found>) -> Walked:
  match ok:
    case True{}:
      Walked{K.hash_of(K.placed(pre, found.sums(out))), root, laid(pre, out)}
    case False{}:
      Refused{"ez: " ++ bad ++ " escapes the package"}

# the found files, placed under the components the package re-roots under
def made.placed(+root: String, +pre: String, +out: List<&2, Found>) -> Walked:
  +bad = K.escaped(K.files_of(K.placed(pre, found.sums(out))))
  made.judge(String.is_empty(bad), bad, root, pre, out)

# a package that climbs no further than the checkout re-roots under as many
# of the entry directory's trailing components as its deepest climb. One that
# climbs further is refused: `K.pkg_of` would have named it after directories
# of the machine it ran on.
def made.anc(far: Bool, +levels: Nat, +dir: String, +out: List<&2, Found>) -> Walked:
  match far:
    case True{}:
      Refused{"ez: the package climbs out of the checkout"}
    case False{}:
      made.placed(P.climb(levels, dir), P.tail(dir, levels), out)

# how many components a checkout-relative directory has: none for the
# checkout's top
def comps(+dir: String) -> Nat:
  +d = P.norm(dir)
  Bool.pick(Nat, Bool.or(String.eq(d, "."), String.is_empty(d)), 0n,
    List.length(&2, String, String.split(d, '/')))

# the deepest climb decided: none leaves the package at the entry's directory
def made.climb(+levels: Nat, +dir: String, +out: List<&2, Found>) -> Walked:
  match levels:
    case 0n:
      made.placed(P.norm(dir), "", out)
    case 1n+p:
      made.anc(Nat.is_gt(1n+p, comps(dir)), 1n+p, dir, out)

# a walk that stopped on a missing file is refused; one that did not is the
# package
def made.go(stop: Bool, +miss: String, +dir: String, +out: List<&2, Found>) -> Walked:
  match stop:
    case True{}:
      Refused{"ez: " ++ miss ++ " is imported but not there"}
    case False{}:
      made.climb(K.climb(found.sums(out)), dir, out)

# the walk's end, judged
def made(+entry: String, st: State) -> Walked:
  State{_seen, out, +miss, _queue} = st
  made.go(Bool.not(String.is_empty(miss)), miss, P.dir(entry), out)

# the package an entry of a checkout would be published as, from the
# checkout's files alone, with this much fuel
def of.fuel(fuel: Nat, +entry: String, +fs: List<&2, Source>) -> Walked:
  made(entry, walk(fuel, fs, P.base(entry), State{[], [], "", [K.Task{entry, ""}]}))

# the same, with the fuel `K.pkg_of` walks with
def of(+entry: String, +fs: List<&2, Source>) -> Walked:
  of.fuel(U32.to_nat(100000), entry, fs)
