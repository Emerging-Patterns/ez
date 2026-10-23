# add/relock: `ez add` as it runs, the add and the lock in one plan
# (EZ-DOC-6). The add is planned as before (`AP.command`, add/plan.bend);
# once it is known to succeed, the plain `ez lock` planner is run over the
# World it leaves (`R.world`, relock/relock.bend): the ledger the add writes,
# the `.bend` files git lists, and the lock's answers. The package the add
# walked is handed to the lock as the answer for its hash, read as a tree
# under BEND_LIB, which is where the add lays it, so it is not read twice; a
# hub package's answers are the ones the add was given. Every other package
# the lock asks about is answered by the lock's interpreter as `ez lock`
# answers it.
#
# The plan, when both succeed: the add's effects, a note when the lock does
# not hold the package added (EZ-DOC-7), then the lock's effects, the lock
# last. When either refuses, a refusal with no effect at all.
import Base
import ./world.bend as A
import ./plan.bend as AP
import ./hub.bend as H
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/up.bend as Up
import ../lock/lock.bend as L
import ../ledger/manifest.bend as M
import ../pkg/pkg.bend as K
import ../relock/relock.bend as R

# what `ez add` reads: the add's World, the `.bend` files git lists, and the
# answers to the lock's questions
type World is Data:
  World{add: A.World, listing: W.Listing, locks: List<&2, W.Reply>}

# the add's World
def add(world: World) -> A.World:
  World{a, _listing, _locks} = world
  a

# ---------------------------------------------------------------------------
# the lock's World

# this file's text when it is the one at the path, else the rest's. The rest
# arrives as a thunk, so the first hit ends the scan.
def found.pick(hit: Bool, body: String, rest: Unit -> String) -> String:
  match hit:
    case True{}:
      body
    case False{}:
      rest(Unit{})

# the text of the file at a path among a walk's files, "" when none is there
def text.at(fs: List<&2, K.Source>, +at: String) -> String:
  match fs:
    case []:
      ""
    case K.Source{+p, body} <> t:
      found.pick(String.eq(p, at), body, _u => text.at(t, at))

# the text of each file a manifest names, in its order
def texts(+fs: List<&2, K.Source>, items: List<&2, K.Item>) -> List<&2, String>:
  match items:
    case []:
      []
    case K.Item{at, _sum} <> t:
      text.at(fs, at) <> texts(fs, t)

# the package a walk made, as the answer to the lock's question about its
# hash: its manifest and the text of each file it names, read as a tree under
# BEND_LIB, which is where the add lays it. The lock checks it as it checks
# any tree there. A walk that made no package answers nothing.
def seed.of(walk: K.Walked) -> List<&2, W.Reply>:
  match walk:
    case K.Walked{h, _root, +fs, ss}:
      +manifest = K.manifest_of(ss)
      [W.Reply{W.Pkg{h, L.Hub{}, ""},
        W.Got{W.Lib{}, manifest, texts(fs, L.manifest.files(String.lines(manifest)))}}]
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# the answers the add already has for the lock: a hub package's are those the
# hub gave the add, and a git package's is the package its walk made
def seeds.of(named: Bool, +aw: A.World) -> List<&2, W.Reply>:
  match named:
    case True{}:
      A.hubs(aw)
    case False{}:
      seed.of(AP.walked(aw))

# the answers the add already has for the lock, on the add's World
def seeds(+aw: A.World) -> List<&2, W.Reply>:
  seeds.of(A.named(aw), aw)

# the World a plain `ez lock` reads once the add has run: the ledger it
# writes, the `.bend` files git lists, and the answers it was given, the add's
# first
def lock.world(world: World) -> W.World:
  World{+a, listing, locks} = world
  R.world(A.here(a), R.ledger(AP.command(a), A.ledger(a)), listing,
    List.append(&2, W.Reply, seeds(a), locks))

# the plan of that lock
def lock(world: World) -> P.Plan:
  P.plan(lock.world(world))

# ---------------------------------------------------------------------------
# the note (EZ-DOC-7)

# the hash of the package the add records
def added.of(named: Bool, +aw: A.World) -> String:
  match named:
    case True{}:
      H.hash(aw)
    case False{}:
      AP.hash(aw)

# the hash of the package the add records, on the add's World
def added(+aw: A.World) -> String:
  added.of(A.named(aw), aw)

# whether the lock holds a package under the hash
def held(ps: List<&2, L.Pack>, +hash: String) -> Bool:
  match ps:
    case []:
      False{}
    case h <> t:
      L.any.step(String.eq(L.pack.hash(h), hash), _u => held(t, hash))

# the line that says the lock does not hold it
def unlocked(+hash: String) -> String:
  "ez: no .bend file git lists imports " ++ hash ++ " yet, so ez.lock.toml does " ++
    "not hold it. Import it, `git add` the file, and run `ez lock`."

# the note: the line when the lock does not hold the package, none when it does
def notes.of(held: Bool, +hash: String) -> List<&2, P.Effect>:
  match held:
    case True{}:
      []
    case False{}:
      [P.Say{unlocked(hash)}]

# the note on a World
def notes(+world: World) -> List<&2, P.Effect>:
  notes.of(held(P.packs(lock.world(world)), added(add(world))), added(add(world)))

# ---------------------------------------------------------------------------
# the plan

# what is added after the lock's reason when the lock refuses: that nothing
# was written, and, when the add moves a dependency's hash, where the old one
# may still be imported from
def moved.of(moved: Bool, +name: String, +old: String, +new: String) -> String:
  match moved:
    case True{}:
      "\nez: ez add moves " ++ name ++ " from " ++ old ++ " to " ++ new ++
        "; a .bend file that imports " ++ old ++ " has to name " ++ new ++
        " first, or `ez lock --upgrade --package " ++ name ++ "` moves it"
    case False{}:
      ""

def tail.dep(+dep: M.Dep, +old: M.Dep) -> String:
  "\nez: ez add wrote nothing, since it writes ez.toml and ez.lock.toml together" ++
    moved.of(Bool.and(Bool.not(String.is_empty(M.dep.hash(old))),
      Bool.not(String.eq(M.dep.hash(old), M.dep.hash(dep)))),
      M.dep.name(dep), M.dep.hash(old), M.dep.hash(dep))

# the dependency the add records
def dep.of(named: Bool, +aw: A.World) -> M.Dep:
  match named:
    case True{}:
      H.added(aw)
    case False{}:
      AP.added(aw)

# what is added after the lock's reason, on the add's World
def tail(+aw: A.World) -> String:
  +dep = dep.of(A.named(aw), aw)
  tail.dep(dep, M.find(A.deps(aw), M.dep.name(dep)))

# `ez add` over a World: the add, then the lock over what it leaves
def plan(world: World) -> P.Plan:
  World{+a, +listing, +locks} = world
  R.join(AP.command(a), lock(World{a, listing, locks}), notes(World{a, listing, locks}),
    tail(a))

# whether `ez add` refuses on a World
def refuses(world: World) -> Bool:
  R.refuses(plan(world))

# ---------------------------------------------------------------------------
# the step

# what the interpreter does next: answer git's questions or the hub's for the
# add, answer the lock's, or run the plan
type Next is Data:
  AskGit{asks: List<&2, Up.Ask>}
  AskHub{asks: List<&2, W.Ask>}
  AskLock{asks: List<&2, W.Ask>}
  Planned{plan: P.Plan}

# the lock's step, once the add is planned and succeeds
def next.lock(st: P.Step, +world: World) -> Next:
  match st:
    case P.Asking{as, ups, ns}:
      AskLock{R.asks(P.Asking{as, ups, ns})}
    case P.Run{_pl}:
      Planned{plan(world)}

# the add's plan made: refused, it is the plan; otherwise the lock is next
def next.made(refused: Bool, +world: World) -> Next:
  match refused:
    case True{}:
      Planned{plan(world)}
    case False{}:
      next.lock(P.step(lock.world(world)), world)

def next.add(nx: AP.Next, +world: World) -> Next:
  match nx:
    case AP.AskGit{asks}:
      AskGit{asks}
    case AP.AskHub{asks}:
      AskHub{asks}
    case AP.Planned{pl}:
      next.made(R.refuses(pl), world)

# what the interpreter does next on a World
def next(+world: World) -> Next:
  next.add(AP.next(add(world)), world)
