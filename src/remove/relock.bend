# remove/relock: `ez remove` as it runs, the remove and the lock in one plan
# (EZ-DOC-6). The remove is planned as before (`RP.plan`, remove/plan.bend);
# once it is known to succeed, the plain `ez lock` planner is run over the
# World it leaves (`R.world`, relock/relock.bend): the ledger the remove
# writes, the `.bend` files git lists, and the lock's answers, which the
# lock's interpreter gives as `ez lock` gives them.
#
# The plan, when both succeed: the remove's effects, then the lock's, the
# lock last. When either refuses, a refusal with no effect at all. A `.bend`
# file git lists that still imports the dependency removed makes the lock
# refuse, since ez.toml no longer names it, and so the remove.
import Base
import ./plan.bend as RP
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../relock/relock.bend as R

# what `ez remove` reads: the remove's World, the directory it runs in, the
# `.bend` files git lists, and the answers to the lock's questions
type World is Data:
  World{remove: RP.World, here: String, listing: W.Listing, locks: List<&2, W.Reply>}

# the remove's World
def remove(world: World) -> RP.World:
  World{r, _here, _listing, _locks} = world
  r

# the ledger's text the remove read
def ledger.was(rw: RP.World) -> Maybe<&2, String>:
  RP.World{_n, l, _ig} = rw
  l

# the World a plain `ez lock` reads once the remove has run
def lock.world(world: World) -> W.World:
  World{+r, +here, listing, locks} = world
  R.world(here, R.ledger(RP.plan(r), ledger.was(r)), listing, locks)

# the plan of that lock
def lock(world: World) -> P.Plan:
  P.plan(lock.world(world))

# what is added after the lock's reason when the lock refuses
def tail() -> String:
  "\nez: ez remove wrote nothing, since it writes ez.toml and ez.lock.toml together;" ++
    " a .bend file that still imports what it removes has to stop first"

# `ez remove` over a World: the remove, then the lock over what it leaves
def plan(world: World) -> P.Plan:
  World{+r, +here, +listing, +locks} = world
  R.join(RP.plan(r), lock(World{r, here, listing, locks}), [], tail())

# whether `ez remove` refuses on a World
def refuses(world: World) -> Bool:
  R.refuses(plan(world))

# what the interpreter does next: answer the lock's questions, or run the plan
type Next is Data:
  AskLock{asks: List<&2, W.Ask>}
  Planned{plan: P.Plan}

# the lock's step, once the remove succeeds
def next.lock(st: P.Step, +world: World) -> Next:
  match st:
    case P.Asking{as, ups, ns}:
      AskLock{R.asks(P.Asking{as, ups, ns})}
    case P.Run{_pl}:
      Planned{plan(world)}

# the remove refused is the plan; otherwise the lock is next
def next.made(refused: Bool, +world: World) -> Next:
  match refused:
    case True{}:
      Planned{plan(world)}
    case False{}:
      next.lock(P.step(lock.world(world)), world)

# what the interpreter does next on a World
def next(+world: World) -> Next:
  next.made(R.refuses(RP.plan(remove(world))), world)
