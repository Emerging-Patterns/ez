# ws/relock: `ez add` and `ez remove` in a workspace (EZ-WS-10). Outside a
# workspace each runs its command's plan joined to a plain lock over the
# ledger it writes (add/relock.bend, remove/relock.bend, EZ-DOC-6). In a
# workspace the lock that ledger belongs to is the root's, so the command's
# own plan is joined instead to the plan a plain `ez lock` at the root makes
# (`U.plan`, ws/up.bend) over the workspace the command leaves: the root's
# ledger and every member's as git lists them, with the one the command
# writes in place of its own, joined (ws/joint.bend), the `.bend` files git
# lists under the root, and the lock's answers. The command runs where it
# is, so every path that lock writes is taken from the root's directory
# (`at.effect`), and no lock is written in a member.
#
# A ledger the add or remove writes at the root is written through the
# ledger model, which holds no `[workspace]` table, so it is written back with
# the table it had (`U.root.text`), as an upgrade writes the root's.
import Base
import ../lock/plan.bend as LP
import ../lock/world.bend as LW
import ../lock/lock.bend as L
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../pkg/path.bend as P
import ../relock/relock.bend as R
import ../add/world.bend as A
import ../add/plan.bend as AP
import ../add/relock.bend as AR
import ../remove/plan.bend as RP
import ../remove/relock.bend as RR
import ./workspace.bend as W
import ./joint.bend as J
import ./up.bend as U

# what a command run in a workspace reads of its root: the root's directory,
# the path from it to where the command runs, the root's ledger, every other
# ez.toml git lists under it, the `.bend` files git lists under it, each path
# from the root, and the root's lock
type Rooted is Data:
  Rooted{
    at: String,
    rel: List<&2, String>,
    text: String,
    found: List<&2, J.Found>,
    listing: LW.Listing,
    lock: String
  }

# where a command runs: in a project of its own, or in a workspace
type Ws is Data:
  Own{}
  Inside{root: Rooted}

# the root's directory
def rooted.at(root: Rooted) -> String:
  Rooted{at, _rel, _text, _found, _listing, _lock} = root
  at

# ---------------------------------------------------------------------------
# the root's lock, run from where the command runs

# a place a tree is laid in, taken from the root: the root's committed
# `.ez/lib` for a committed tree, BEND_LIB as it is, and a directory under the
# root from the root
def at.place(+at: String, place: LP.Place) -> LP.Place:
  match place:
    case LP.Committed{}:
      LP.Under{at}
    case LP.Cache{}:
      LP.Cache{}
    case LP.Under{dir}:
      LP.Under{P.join(at, dir)}

# an effect of the root's lock as it is run from where the command runs:
# every path it writes taken from the root. Removing a committed tree is
# laying it with no file, which removes what was there and writes nothing.
def at.effect(+at: String, effect: LP.Effect) -> LP.Effect:
  match effect:
    case LP.Write{path, text}:
      LP.Write{P.join(at, path), text}
    case LP.Lay{place, hash, files}:
      LP.Lay{at.place(at, place), hash, files}
    case LP.Drop{hash}:
      LP.Lay{LP.Under{at}, hash, []}
    case LP.Say{text}:
      LP.Say{text}
    case LP.Name{nv, hash}:
      LP.Name{nv, hash}

# every effect of the root's lock, so
def at.effects(+at: String, es: List<&2, LP.Effect>) -> List<&2, LP.Effect>:
  match es:
    case []:
      []
    case hd <> tl:
      at.effect(at, hd) <> at.effects(at, tl)

# the root's lock plan, so
def at.plan(+at: String, pl: LP.Plan) -> LP.Plan:
  LP.Plan{es, outcome} = pl
  LP.Plan{at.effects(at, es), outcome}

# ---------------------------------------------------------------------------
# the root's ledger, keeping its `[workspace]` table

# a ledger the command writes at the root, once it is read: as the root's
# with the table it had, or as it is when it does not read
def keep.parsed(rd: M.Read, +spec: W.Spec, root: W.Root, +text: String) -> String:
  match rd:
    case M.Good{mm}:
      U.root.text(mm, spec, root)
    case M.Bad{_why}:
      text

# once it is known whether the root's ledger, `old`, had a `[workspace]`
# table
def keep.read(rd: W.Read, +old: String, +text: String) -> String:
  match rd:
    case W.Root{+spec}:
      keep.parsed(M.parse(text), spec, W.root.of(old), text)
    case W.Lone{}:
      text
    case W.Bad{_why}:
      text

# the text a command writes as the root's ledger, which held `old`
def keep(+old: String, +text: String) -> String:
  keep.read(W.spec.of(old), old, text)

# a file the command writes, once it is known whether it is the ledger
def keep.write(hit: Bool, +old: String, +path: String, +text: String) -> LP.Effect:
  match hit:
    case True{}:
      LP.Write{path, keep(old, text)}
    case False{}:
      LP.Write{path, text}

# an effect of the command at the root, its ledger keeping its table
def keep.effect(+old: String, effect: LP.Effect) -> LP.Effect:
  match effect:
    case LP.Write{+path, text}:
      keep.write(String.eq(path, R.toml()), old, path, text)
    case LP.Lay{place, hash, files}:
      LP.Lay{place, hash, files}
    case LP.Drop{hash}:
      LP.Drop{hash}
    case LP.Say{text}:
      LP.Say{text}
    case LP.Name{nv, hash}:
      LP.Name{nv, hash}

# every effect of the command at the root, so
def keep.effects(+old: String, es: List<&2, LP.Effect>) -> List<&2, LP.Effect>:
  match es:
    case []:
      []
    case hd <> tl:
      keep.effect(old, hd) <> keep.effects(old, tl)

# the command's own plan, run at the path `rel` from the root, whose ledger
# is `old`: at the root, with the root's ledger keeping its table, and in a
# member as it is
def edit.at(rel: List<&2, String>, +old: String, pl: LP.Plan) -> LP.Plan:
  match rel:
    case []:
      LP.Plan{es, outcome} = pl
      LP.Plan{keep.effects(old, es), outcome}
    case _hd <> _tl:
      pl

# the command's own plan, in the workspace
def edit(root: Rooted, pl: LP.Plan) -> LP.Plan:
  Rooted{_at, rel, text, _found, _listing, _lock} = root
  edit.at(rel, text, pl)

# ---------------------------------------------------------------------------
# the ledgers the command leaves

# the root's ledger and every other ez.toml git lists under the root
type Ledgers is Data:
  Ledgers{text: String, found: List<&2, J.Found>}

# a listed ez.toml, once it is known whether it is the one the command writes
def put.pick(hit: Bool, +path: String, was: String, +text: String, rest: List<&2, J.Found>) -> List<&2, J.Found>:
  match hit:
    case True{}:
      J.Found{path, text} <> rest
    case False{}:
      J.Found{path, was} <> rest

# every listed ez.toml, the one at `path` holding `text`
def put.found(fs: List<&2, J.Found>, +path: String, +text: String) -> List<&2, J.Found>:
  match fs:
    case []:
      []
    case J.Found{+fp, ft} <> tl:
      rest = put.found(tl, path, text)
      put.pick(String.eq(fp, path), fp, ft, text, rest)

# the ledgers once the command at `rel` writes `new`: the root's, at the
# root, or the member's ez.toml under it
def ledgers.at(rel: List<&2, String>, +new: String, +text: String, +fs: List<&2, J.Found>) -> Ledgers:
  match rel:
    case []:
      Ledgers{new, fs}
    case hd <> tl:
      Ledgers{text, put.found(fs, P.join(W.segs.text(hd <> tl), R.toml()), new)}

# the ledger's text the command leaves, "" when it leaves none, which only a
# command that refuses does
def new.of(led: Maybe<&2, String>) -> String:
  match led:
    case None{}:
      ""
    case Some{text}:
      text

# the ledgers the command leaves, when its own plan, as the workspace runs it,
# is `pl` and its ledger held `was` before
def ledgers(root: Rooted, pl: LP.Plan, was: Maybe<&2, String>) -> Ledgers:
  Rooted{_at, rel, +text, fs, _listing, _lock} = root
  ledgers.at(rel, new.of(R.ledger(pl, was)), text, fs)

# ---------------------------------------------------------------------------
# the root's lock

# the lock at the root, as a plain `ez lock` there plans it: what its upgrade
# half needs and the World it reads, or why the ledgers cannot be joined
type Lock is Data:
  Lock{back: U.Back, world: LW.World}
  Stop{why: String}

# the World a plain `ez lock` reads at the root
def world(+at: String, led: Maybe<&2, String>, listing: LW.Listing, rs: List<&2, LW.Reply>) -> LW.World:
  LW.World{LW.Args{False{}, "", at}, led, listing, rs, []}

# the lock, once the ledgers were joined: as `ez lock` at the root reads it
# (ws/run.bend's `joint.at`), with the members' answers first
def lock.joint(
  jj: J.Joint,
  +at: String,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +listing: LW.Listing,
  +lock: String,
  rs: List<&2, LW.Reply>
) -> Lock:
  match jj:
    case J.Lone{}:
      Lock{U.Alone{}, world(at, Some{text}, listing, rs)}
    case J.Clash{why}:
      Stop{why}
    case J.Joint{+mm}:
      Lock{U.Back{text, spec, fs, lock},
        world(at, Some{Rend.show(mm)}, listing,
          List.append(&2, LW.Reply, J.seeds(J.Joint{mm}, J.files(listing)), rs))}

# the lock, once the root's ledger is read
def lock.read(
  rd: W.Read,
  +at: String,
  +text: String,
  +fs: List<&2, J.Found>,
  +listing: LW.Listing,
  +lock: String,
  rs: List<&2, LW.Reply>
) -> Lock:
  match rd:
    case W.Lone{}:
      Lock{U.Alone{}, world(at, Some{text}, listing, rs)}
    case W.Bad{why}:
      Stop{why}
    case W.Root{+spec}:
      lock.joint(J.joint(text, fs, J.files(listing)), at, text, spec, fs, listing, lock, rs)

# the lock at the root over the ledgers the command leaves
def lock.of(lg: Ledgers, root: Rooted, rs: List<&2, LW.Reply>) -> Lock:
  Ledgers{+text, +fs} = lg
  Rooted{+at, _rel, _text, _found, +listing, +lock} = root
  lock.read(W.spec.of(text), at, text, fs, listing, lock, rs)

# a refusal, with no effect
def stop(+why: String) -> LP.Plan:
  LP.Plan{[], LP.Refused{why}}

# the lock's plan
def lock.plan(lk: Lock) -> LP.Plan:
  match lk:
    case Lock{back, +world}:
      U.plan(back, world)
    case Stop{why}:
      stop(why)

# the lock's step
def lock.step(lk: Lock) -> LP.Step:
  match lk:
    case Lock{+back, +world}:
      U.step(back, world)
    case Stop{why}:
      LP.Run{stop(why)}

# the packages the lock records, none when it cannot be made
def lock.packs(lk: Lock) -> List<&2, L.Pack>:
  match lk:
    case Lock{_back, +world}:
      LP.packs(world)
    case Stop{_why}:
      []

# ---------------------------------------------------------------------------
# `ez add`

# the add's own plan, as the workspace runs it
def add.edit(+root: Rooted, +aw: A.World) -> LP.Plan:
  edit(root, AP.command(aw))

# the root's lock over what the add leaves, with the answers the add has for
# it first
def add.lock(+root: Rooted, world: AR.World) -> Lock:
  AR.World{+aw, _listing, locks} = world
  lock.of(ledgers(root, add.edit(root, aw), A.ledger(aw)), root,
    List.append(&2, LW.Reply, AR.seeds(aw), locks))

# the note (EZ-DOC-7), over the root's lock
def add.notes(+lk: Lock, +aw: A.World) -> List<&2, LP.Effect>:
  AR.notes.of(AR.held(lock.packs(lk), AR.added(aw)), AR.added(aw))

# `ez add` in a workspace: the add, then the root's lock over what it leaves,
# run from where the add runs
def add.plan(+root: Rooted, world: AR.World) -> LP.Plan:
  AR.World{+aw, +listing, +locks} = world
  +lk = add.lock(root, AR.World{aw, listing, locks})
  R.join(add.edit(root, aw), at.plan(rooted.at(root), lock.plan(lk)), add.notes(lk, aw), AR.tail(aw))

# the lock's step, once the add is planned and succeeds
def add.next.lock(st: LP.Step, +root: Rooted, +world: AR.World) -> AR.Next:
  match st:
    case LP.Asking{as, ups, ns}:
      AR.AskLock{R.asks(LP.Asking{as, ups, ns})}
    case LP.Run{_pl}:
      AR.Planned{add.plan(root, world)}

# the add's plan made: refused, it is the plan; otherwise the lock is next
def add.next.made(refused: Bool, +root: Rooted, +world: AR.World) -> AR.Next:
  match refused:
    case True{}:
      AR.Planned{add.plan(root, world)}
    case False{}:
      add.next.lock(lock.step(add.lock(root, world)), root, world)

# the add's own step: its questions, or its plan made
def add.next.add(nx: AP.Next, +root: Rooted, +world: AR.World) -> AR.Next:
  match nx:
    case AP.AskGit{asks}:
      AR.AskGit{asks}
    case AP.AskHub{asks}:
      AR.AskHub{asks}
    case AP.Planned{pl}:
      add.next.made(R.refuses(pl), root, world)

# what the interpreter does next for `ez add`: in a project of its own, what
# add/relock.bend says; in a workspace, the add, then the root's lock
def add.next(ws: Ws, +world: AR.World) -> AR.Next:
  match ws:
    case Own{}:
      AR.next(world)
    case Inside{+root}:
      add.next.add(AP.next(AR.add(world)), root, world)

# `ez add`'s plan, wherever it runs
def add.planned(ws: Ws, world: AR.World) -> LP.Plan:
  match ws:
    case Own{}:
      AR.plan(world)
    case Inside{+root}:
      add.plan(root, world)

# ---------------------------------------------------------------------------
# `ez remove`

# the remove's own plan, as the workspace runs it
def remove.edit(+root: Rooted, +rw: RP.World) -> LP.Plan:
  edit(root, RP.plan(rw))

# the root's lock over what the remove leaves
def remove.lock(+root: Rooted, world: RR.World) -> Lock:
  RR.World{+rw, _here, _listing, locks} = world
  lock.of(ledgers(root, remove.edit(root, rw), RR.ledger.was(rw)), root, locks)

# `ez remove` in a workspace: the remove, then the root's lock over what it
# leaves, run from where the remove runs
def remove.plan(+root: Rooted, world: RR.World) -> LP.Plan:
  RR.World{+rw, +here, +listing, +locks} = world
  +lk = remove.lock(root, RR.World{rw, here, listing, locks})
  R.join(remove.edit(root, rw), at.plan(rooted.at(root), lock.plan(lk)), [], RR.tail())

# the lock's step, once the remove succeeds
def remove.next.lock(st: LP.Step, +root: Rooted, +world: RR.World) -> RR.Next:
  match st:
    case LP.Asking{as, ups, ns}:
      RR.AskLock{R.asks(LP.Asking{as, ups, ns})}
    case LP.Run{_pl}:
      RR.Planned{remove.plan(root, world)}

# the remove refused is the plan; otherwise the lock is next
def remove.next.made(refused: Bool, +root: Rooted, +world: RR.World) -> RR.Next:
  match refused:
    case True{}:
      RR.Planned{remove.plan(root, world)}
    case False{}:
      remove.next.lock(lock.step(remove.lock(root, world)), root, world)

# what the interpreter does next for `ez remove`: in a project of its own,
# what remove/relock.bend says; in a workspace, the remove, then the root's
# lock
def remove.next(ws: Ws, +world: RR.World) -> RR.Next:
  match ws:
    case Own{}:
      RR.next(world)
    case Inside{+root}:
      remove.next.made(R.refuses(RP.plan(RR.remove(world))), root, world)

# `ez remove`'s plan, wherever it runs
def remove.planned(ws: Ws, world: RR.World) -> LP.Plan:
  match ws:
    case Own{}:
      RR.plan(world)
    case Inside{+root}:
      remove.plan(root, world)
