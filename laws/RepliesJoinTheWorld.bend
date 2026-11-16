# Each round of a command's interpreter adds the answers it got to the World
# the planner reads, and nothing else: the new answers go after the ones the
# World held, in the order they came, and every other field is the World's
# own. So the planner, which never asks what its World answers already, sees
# each answer once and loses none, whatever the round.
#
# Internal, not interface: this holds the interpreters' bookkeeping in place.
# That the answers are what the other program printed is trusted in
# src/ez/app.bend.
import Base
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/fetch/world.bend as F
import ../src/doctor/world.bend as DW
import ../src/pub/world.bend as PW
import ../src/tool/world.bend as TW
import ../src/add/world.bend as A
import ../src/add/relock.bend as AR
import ../src/remove/relock.bend as RR
import ../src/remove/plan.bend as RP

# LAW: `ez lock` and `ez lock --upgrade` add the hub's and git's answers after
# the ones the World held, each to its own list
law lock_replies_join:
  for args: W.Args
  for ledger: Maybe<&2, String>
  for listing: W.Listing
  for replies: List<&2, W.Reply>
  for ups: List<&2, Up.Reply>
  for rs: List<&2, W.Reply>
  for us: List<&2, Up.Reply>
  {W.more(W.World{args, ledger, listing, replies, ups}, rs, us)
    == W.World{args, ledger, listing, List.append(&2, W.Reply, replies, rs),
      List.append(&2, Up.Reply, ups, us)} : W.World}

# LAW: `ez fetch` adds its answers after the ones the World held
law fetch_replies_join:
  for here: String
  for ledger: Bool
  for lock: Maybe<&2, String>
  for replies: List<&2, F.Reply>
  for rs: List<&2, F.Reply>
  {F.more(F.World{here, ledger, lock, replies}, rs)
    == F.World{here, ledger, lock, List.append(&2, F.Reply, replies, rs)} : F.World}

# LAW: `ez doctor` adds its answers after the ones the World held
law doctor_replies_join:
  for cc: String
  for lib: String
  for ledger: Maybe<&2, String>
  for lock: Maybe<&2, String>
  for replies: List<&2, DW.Reply>
  for rs: List<&2, DW.Reply>
  {DW.more(DW.World{cc, lib, ledger, lock, replies}, rs)
    == DW.World{cc, lib, ledger, lock, List.append(&2, DW.Reply, replies, rs)} : DW.World}

# LAW: `ez publish` adds its answers after the ones the World held
law publish_replies_join:
  for here: String
  for ledger: Maybe<&2, String>
  for replies: List<&2, PW.Reply>
  for rs: List<&2, PW.Reply>
  {PW.more(PW.World{here, ledger, replies}, rs)
    == PW.World{here, ledger, List.append(&2, PW.Reply, replies, rs)} : PW.World}

# LAW: `ez tool` adds its own answers and git's after the ones the World
# held, each to its own list
law tool_replies_join:
  for act: TW.Act
  for target: String
  for want: String
  for here: String
  for env: TW.Env
  for bend: String
  for ledger: Maybe<&2, String>
  for lock: Maybe<&2, String>
  for replies: List<&2, TW.Reply>
  for ups: List<&2, Up.Reply>
  for rs: List<&2, TW.Reply>
  for us: List<&2, Up.Reply>
  {TW.more(TW.World{act, target, want, here, env, bend, ledger, lock, replies, ups}, rs, us)
    == TW.World{act, target, want, here, env, bend, ledger, lock,
      List.append(&2, TW.Reply, replies, rs), List.append(&2, Up.Reply, ups, us)} : TW.World}

# LAW: `ez add` adds git's answers after the ones the add's World held
law add_replies_join:
  for args: A.Args
  for here: String
  for home: String
  for ledger: Maybe<&2, String>
  for ignore: String
  for replies: List<&2, Up.Reply>
  for hubs: List<&2, W.Reply>
  for rs: List<&2, Up.Reply>
  {A.more(A.World{args, here, home, ledger, ignore, replies, hubs}, rs)
    == A.World{args, here, home, ledger, ignore, List.append(&2, Up.Reply, replies, rs), hubs}
    : A.World}

# LAW: and the hub's after the hub's
law add_hub_replies_join:
  for args: A.Args
  for here: String
  for home: String
  for ledger: Maybe<&2, String>
  for ignore: String
  for replies: List<&2, Up.Reply>
  for hubs: List<&2, W.Reply>
  for rs: List<&2, W.Reply>
  {A.more.hub(A.World{args, here, home, ledger, ignore, replies, hubs}, rs)
    == A.World{args, here, home, ledger, ignore, replies, List.append(&2, W.Reply, hubs, rs)}
    : A.World}

# LAW: the add's relock World passes both on to the add's World, leaving its
# own listing and answers as they were
law add_relock_replies_join:
  for a: A.World
  for listing: W.Listing
  for locks: List<&2, W.Reply>
  for rs: List<&2, Up.Reply>
  for hs: List<&2, W.Reply>
  {AR.more.hub(AR.more(AR.World{a, listing, locks}, rs), hs)
    == AR.World{A.more.hub(A.more(a, rs), hs), listing, locks} : AR.World}

# LAW: and the relock's after the relock's, leaving the add's World as it was
law add_lock_replies_join:
  for a: A.World
  for listing: W.Listing
  for locks: List<&2, W.Reply>
  for rs: List<&2, W.Reply>
  {AR.more.lock(AR.World{a, listing, locks}, rs)
    == AR.World{a, listing, List.append(&2, W.Reply, locks, rs)} : AR.World}

# LAW: `ez remove` adds the relock's answers after the ones the World held
law remove_replies_join:
  for r: RP.World
  for here: String
  for listing: W.Listing
  for locks: List<&2, W.Reply>
  for rs: List<&2, W.Reply>
  {RR.more(RR.World{r, here, listing, locks}, rs)
    == RR.World{r, here, listing, List.append(&2, W.Reply, locks, rs)} : RR.World}
