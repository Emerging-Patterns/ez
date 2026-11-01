# `ez init` writes nothing when a ledger exists, and `ez add`, `ez remove`,
# `ez fetch` and `ez lock`, with or without `--upgrade`, refuse and write
# nothing when there is none.
import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../src/init/plan.bend as IP
import ../src/remove/plan.bend as RP

# LAW: with no ez.toml, `ez lock` refuses, plain or `--upgrade`, whatever
# else the World holds, so with `lock_refusal_writes_nothing` it writes
# nothing
law lock_needs_ledger:
  for up: Bool
  for +only: String
  for here: String
  for listing: W.Listing
  for rs: List<&2, W.Reply>
  for us: List<&2, Up.Reply>
  {P.refuses(W.World{W.Args{up, only, here}, None{}, listing, rs, us}) == True{} : Bool}

# LAW: with no ez.toml, `ez add` refuses, whatever it was asked to add, a
# hub package's name included
law add_needs_ledger:
  for +a: A.Args
  for +here: String
  for +home: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  {AP.refuses.command(A.World{a, here, home, None{}, ignore, rs, hs}) == True{} : Bool}

# LAW: and asks nothing first, of a remote or of the hub
law add_needs_ledger_asks_nothing:
  for +a: A.Args
  for +here: String
  for +home: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  {AP.next.asks(AP.next(A.World{a, here, home, None{}, ignore, rs, hs})) == False{} : Bool}

# LAW: with no ez.toml, `ez fetch` refuses, whatever the lock says
law fetch_needs_ledger:
  for +here: String
  for got: Maybe<&2, String>
  for rs: List<&2, F.Reply>
  {FP.refuses(F.World{here, False{}, got, rs}) == True{} : Bool}

# LAW: and asks nothing first
law fetch_needs_ledger_asks_nothing:
  for +here: String
  for got: Maybe<&2, String>
  for rs: List<&2, F.Reply>
  {FP.wants(F.World{here, False{}, got, rs}) == [] : List<&2, F.Ask>}

# LAW: a ledger already on disk, whatever it holds, leaves `ez init` nothing
# to write, whatever it was asked for and whatever else is there, so the
# ledger's dependencies, tools and `bin` survive a second `ez init`
law init_keeps_ledger:
  for name: String
  for entry: String
  for desc: String
  for s: String
  for ignore: Maybe<&2, String>
  for main: Maybe<&2, String>
  for lib: Maybe<&2, String>
  {P.writes(IP.plan(IP.World{name, entry, desc, Some{s}, ignore, main, lib})) == False{} : Bool}

# LAW: with no ez.toml, `ez remove` refuses, whatever it was asked to remove
# and whatever `.gitignore` holds, so it writes nothing
law remove_needs_ledger:
  for +name: String
  for +ignore: String
  {RP.refuses(RP.World{name, None{}, ignore}) == True{} : Bool}
