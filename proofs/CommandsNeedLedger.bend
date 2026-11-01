# proofs of laws/CommandsNeedLedger.bend
import Base
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../laws/CommandsNeedLedger.bend as Laws

# No ledger reads as a `Bad`, which a plain lock takes as it is and an
# upgrade leaves as it is, and `need.why` refuses it.
def Laws.lock_needs_ledger(up, _only, _here, _listing, _rs, _us):
  match up:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a plan with no ledger refuses, whichever planner runs, and the step
# asks nothing
law command_no_ledger:
  for b: Bool
  for +a: A.Args
  for +here: String
  for +home: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  {AP.refuses.plan(AP.command.of(b, A.World{a, here, home, None{}, ignore, rs, hs}))
    == True{} : Bool}

def command_no_ledger(b, _a, _here, _home, _ignore, _rs, _hs):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law next_no_ledger:
  for b: Bool
  for +a: A.Args
  for +here: String
  for +home: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  {AP.next.asks(AP.next.of(b, A.World{a, here, home, None{}, ignore, rs, hs})) == False{}
    : Bool}

def next_no_ledger(b, _a, _here, _home, _ignore, _rs, _hs):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# No ledger reads as the `Bad` arm, which stops before anything is asked.
def Laws.add_needs_ledger(a, here, home, ignore, rs, hs):
  command_no_ledger(A.named(A.World{a, here, home, None{}, ignore, rs, hs}), a, here, home,
    ignore, rs, hs)

def Laws.add_needs_ledger_asks_nothing(a, here, home, ignore, rs, hs):
  next_no_ledger(A.named(A.World{a, here, home, None{}, ignore, rs, hs}), a, here, home,
    ignore, rs, hs)

# No ledger is the arm that refuses before anything else.
def Laws.fetch_needs_ledger(_here, _got, _rs):
  {==}

def Laws.fetch_needs_ledger_asks_nothing(_here, _got, _rs):
  {==}

# A ledger that is there picks the arm that plans nothing.
def Laws.init_keeps_ledger(_name, _entry, _desc, _s, _ignore, _main, _lib):
  {==}

# No ledger reads as the `Bad` arm, which refuses.
def Laws.remove_needs_ledger(_name, _ignore):
  {==}
