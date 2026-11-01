# `ez doctor` reports a lock that `ez lock` would not write as it stands,
# judged without the network from the ledger, the committed sources and the
# trees under `BEND_LIB`, and exits 1 when it reports one or cannot judge it.
#
# This guarantee is proved over the plan `ez doctor` runs
# (`src/doctor/plan.bend`). `DP.relock(w, fs)` is the World doctor puts to
# the lock planner: a plain `ez lock` over the ledger's text, the sources
# `fs` git listed, and every tree doctor read from `BEND_LIB`, a hub
# package's judged as the hub's bytes and a git package's as `ez lock`
# judges one it finds there. When a lock is there and the lock planner asks
# nothing more, a lock whose text is the one `P.decide` makes is said to be
# up to date, and that line is not a problem (`doctor_passes_fresh_lock`,
# `doctor_says_fresh_lock`); a lock whose text differs by any byte is said
# to be out of date and fails the command (`doctor_reports_stale_lock`,
# `doctor_stale_lock_fails`). When the lock planner still asks about a
# package, which doctor asks `BEND_LIB` for and never the network, the lock
# is not checked and the command fails (`doctor_unchecked_lock_fails`). The
# lock planner answers the names it asks about from the lock and the names
# files under `BEND_LIB`, never the hub, and when it still asks about one
# the lock is not checked either (`doctor_unchecked_names_fail`); the laws
# before it hold when it asks nothing more about names. What the laws take
# from the interpreter is trusted in src/ez/app.bend: that a tree's answer
# is its manifest and files as they are under `BEND_LIB`, and that a tree it
# reports absent has no manifest there.
#
# `DP.relock(w, fs)` is the World doctor puts to the lock planner over the
# sources `fs`: a plain `ez lock` over the ledger's text, tools and all, the
# lock as it is, every tree the World read from BEND_LIB, and every name's
# file it read there. `P.wants` of it is what the lock planner still asks
# about packages, which once doctor has asked everything it can is the
# packages BEND_LIB lacks, `P.wants.names` what it still asks about names,
# which is the names whose files BEND_LIB lacks, and `P.decide` of its
# inputs is the lock `ez lock` would write, or why it would write none.
# `DP.checked(w)` is what doctor says of the lock against it.
import Base
import ../src/lock/plan.bend as P
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/lock/world.bend as W

# LAW: a lock the lock planner would write as it stands is not reported stale:
# when a lock is there, the sources were listed, the lock planner has every
# answer it asks for on the World doctor gathered, about packages and about
# names, and the lock it decides on
# is the lock's text byte for byte, the check's one line is that the lock is
# up to date, and it is not a problem
law doctor_passes_fresh_lock:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{t} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  {DP.checked(w) == [DP.Note{False{}, DP.fresh.line()}] : List<&2, DP.Note>}

# LAW: and doctor says so
law doctor_says_fresh_lock:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{t} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  {DP.said(DP.plan(w), DP.fresh.line()) == True{} : Bool}

# LAW: a lock that differs by any byte from the lock the lock planner decides
# on is reported stale, with the one line that says so
law doctor_reports_stale_lock:
  for +w: DW.World
  for +t: String
  for +u: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{u} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  for ne: {False{} == String.eq(u, t) : Bool}
  {DP.said(DP.plan(w), DP.stale.line()) == True{} : Bool}

# LAW: and a stale lock fails `ez doctor`, so it exits 1
law doctor_stale_lock_fails:
  for +w: DW.World
  for +t: String
  for +u: String
  for +fs: List<&2, W.Source>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {[] == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  for d: {P.Doc{u} == P.decide(W.inputs(DP.relock(w, fs))) : P.Doc}
  for ne: {False{} == String.eq(u, t) : Bool}
  {DP.refuses(w) == True{} : Bool}

# LAW: a lock doctor cannot judge offline, because the lock planner still
# asks about a package BEND_LIB did not hold, fails `ez doctor` too, rather
# than being passed on a guess
law doctor_unchecked_lock_fails:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {a <> as == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.refuses(w) == True{} : Bool}

# LAW: and so does one it cannot judge because the lock planner still asks
# what a name names, whose file BEND_LIB does not hold: doctor never asks the
# hub, so it never judges a name by the network
law doctor_unchecked_names_fail:
  for +w: DW.World
  for +t: String
  for +fs: List<&2, W.Source>
  for +a: W.Ask
  for +as: List<&2, W.Ask>
  for k: {Some{t} == DW.lock(w) : Maybe<&2, String>}
  for l: {DW.Heard{DW.Listed{W.Listed{fs}}} == DW.sources(w) : DW.Heard}
  for o: {[] == P.wants(DP.relock(w, fs)) : List<&2, W.Ask>}
  for on: {a <> as == P.wants.names(DP.relock(w, fs)) : List<&2, W.Ask>}
  {DP.refuses(w) == True{} : Bool}
