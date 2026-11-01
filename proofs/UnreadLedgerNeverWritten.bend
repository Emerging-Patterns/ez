# proofs of laws/UnreadLedgerNeverWritten.bend
import Base
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/remove/plan.bend as RP
import ../laws/UnreadLedgerNeverWritten.bend as Laws

def Laws.read_refuses_a_problem(bad, ss, e):
  %e : {M.read.go(_, M.problem(bad, M.missing(ss)), ss)
    == M.Bad{M.problem(bad, M.missing(ss))} : M.Read}
  {==}

def Laws.render_of_unread_is_blank(_why):
  {==}

# The same once the read is rewritten to the `Bad` the premise gives.
def Laws.lock_refuses_unread(up, only, _here, _s, listing, rs, us, _why, bad):
  match up:
    case True{}:
      %bad : {P.refuses.doc(P.decide(W.inputs.of(Up.next(only, _, us), listing, rs))) == True{}
        : Bool}
      {==}
    case False{}:
      %bad : {P.refuses.doc(P.decide(W.inputs.of(Up.plain(_), listing, rs))) == True{}
        : Bool}
      {==}

# LAW: a ledger that does not parse refuses, whichever planner runs
law command_unread:
  for b: Bool
  for +a: A.Args
  for +here: String
  for +home: String
  for +s: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {AP.refuses.plan(AP.command.of(b, A.World{a, here, home, Some{s}, ignore, rs, hs}))
    == True{} : Bool}

# The read is rewritten to the `Bad` the premise gives, which stops.
def command_unread(b, a, here, home, s, ignore, rs, hs, _why, bad):
  match b:
    case True{}:
      %bad : {AP.refuses.plan(H.plan.v(H.decide.read(_, A.World{a, here, home, Some{s},
        ignore, rs, hs}), A.World{a, here, home, Some{s}, ignore, rs, hs})) == True{} : Bool}
      {==}
    case False{}:
      %bad : {AP.refuses.plan(AP.plan.v(AP.decide.read(_, A.World{a, here, home, Some{s},
        ignore, rs, hs}), A.World{a, here, home, Some{s}, ignore, rs, hs})) == True{} : Bool}
      {==}

def Laws.add_refuses_unread(a, here, home, s, ignore, rs, hs, why, bad):
  command_unread(A.named(A.World{a, here, home, Some{s}, ignore, rs, hs}), a, here, home, s,
    ignore, rs, hs, why, bad)

# The read is rewritten to the `Bad` the premise gives, which refuses.
def Laws.remove_refuses_unread(name, _s, ignore, _why, bad):
  %bad : {RP.refuses.plan(RP.plan.read(_, name, ignore)) == True{} : Bool}
  {==}
