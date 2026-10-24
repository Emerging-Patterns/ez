# relock: what `ez add` and `ez remove` share to leave the lock in step with
# the ledger they write (EZ-DOC-6). Each command plans its edit as before;
# then the plain `ez lock` planner (lock/plan.bend) is run over the World the
# edit leaves: the ledger the edit writes to ez.toml, the `.bend` files git
# lists, and the answers to the lock's questions. The two plans become one:
# the edit's effects, then the lines a person is told about the lock, then the
# lock's effects, which write ez.lock.toml last. A lock that refuses refuses
# the whole command, with no effect at all, so neither file changes.
#
# A plain lock moves no pin (EZ-DOC-5), so every dependency and tool the edit
# did not touch keeps the pin it had, and only what the edit changed is read
# anew.
import Base
import ../lock/plan.bend as P
import ../lock/world.bend as W

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# what ez.toml holds once a plan has run, when it held `was` before
def ledger.of(wrote: P.Wrote, was: Maybe<&2, String>) -> Maybe<&2, String>:
  match wrote:
    case P.Kept{}:
      was
    case P.Put{text}:
      Some{text}

# the ledger an edit leaves, when ez.toml held `was` before it
def ledger(pl: P.Plan, was: Maybe<&2, String>) -> Maybe<&2, String>:
  ledger.of(P.put.plan(pl, toml()), was)

# the World a plain `ez lock` reads, run in `here` over a ledger, the `.bend`
# files git lists, and the answers it was given. It asks the upgrade nothing.
def world(+here: String, ledger: Maybe<&2, String>, listing: W.Listing, rs: List<&2, W.Reply>) -> W.World:
  W.World{W.Args{False{}, "", here}, ledger, listing, rs, []}

# how a plan ends
def outcome(pl: P.Plan) -> P.Outcome:
  P.Plan{_es, o} = pl
  o

# whether a plan ends in a refusal
def refuses(pl: P.Plan) -> Bool:
  P.Plan{_es, o} = pl
  match o:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# the edit and the lock as one plan, once the edit is known to succeed: the
# edit's effects, the notes, and the lock's effects, or, when the lock
# refuses, a refusal with no effect, its reason followed by `tail`
def join.lock(lock: P.Plan, +edit: P.Plan, notes: List<&2, P.Effect>, +tail: String) -> P.Plan:
  P.Plan{es, outcome} = lock
  match outcome:
    case P.Success{}:
      P.Plan{List.append(&2, P.Effect, P.effects(edit), List.append(&2, P.Effect, notes, es)),
        P.Success{}}
    case P.Refused{why}:
      P.Plan{[], P.Refused{why ++ tail}}

def join.edit(refused: Bool, +edit: P.Plan, lock: P.Plan, notes: List<&2, P.Effect>, +tail: String) -> P.Plan:
  match refused:
    case True{}:
      P.Plan{[], P.Refused{P.why(outcome(edit))}}
    case False{}:
      join.lock(lock, edit, notes, tail)

# an edit followed by the lock over what it leaves. An edit that refuses is
# the plan, with no effect; one that succeeds is joined to the lock.
def join(+edit: P.Plan, lock: P.Plan, notes: List<&2, P.Effect>, +tail: String) -> P.Plan:
  join.edit(refuses(edit), edit, lock, notes, tail)

# what the lock still asks, as one list: the packages, then the names. A
# plain lock asks the upgrade nothing.
def asks(st: P.Step) -> List<&2, W.Ask>:
  match st:
    case P.Asking{as, _ups, ns}:
      List.append(&2, W.Ask, as, ns)
    case P.Run{_pl}:
      []
