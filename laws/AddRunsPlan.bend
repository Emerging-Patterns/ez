# The add laws are stated over the plan `ez add` runs (`AP.command`) and the
# questions it asks (`AP.next`), so what they say of the plan is what the
# command does, the interpreter's faithfulness being trusted in
# src/ez/app.bend.
#
# `AP.command` is the git planner's plan (`AP.plan`) for a git or path
# target and the hub planner's (`H.plan`, add/hub.bend) for a hub package's
# `<name>@<version>` (`add_runs_plan`, `add_runs_hub`). The laws of the
# first part are stated over the command; those after them over the planner
# that runs.
#
# `AP.added(w)` is the dependency the git plan records and `H.added(w)` the
# one the hub plan records: every law about them holds of every World, and
# `add_edits_ledger` and `add_named_edits_ledger` say an add that does not
# refuse writes exactly it into ez.toml, through `Rend.add.keep`.
import Base
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP

# LAW: a target that is not a hub package's name runs the git planner
law add_runs_plan:
  for +w: A.World
  for g: {A.named(w) == False{} : Bool}
  {AP.command(w) == AP.plan(w) : P.Plan}
