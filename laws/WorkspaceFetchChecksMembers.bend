# In a workspace, `ez fetch` lays every package the root lock records, and
# lays a member's package from the committed tree only when its walk hashes to
# the hash the lock records for it; otherwise it refuses, names the member,
# and lays nothing.
#
# also rests on: laws/FetchLaysTheLock.bend,
# laws/FetchRefusalWritesNothing.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# ---------------------------------------------------------------------------
# a workspace member's package (laws/WorkspaceFetchChecksMembers.bend)

# LAW: a member's package is asked for as the committed files, under the hash
# the lock records it by
law fetch_member_asks_tree:
  for path: String
  for +entry: String
  for here: String
  for hub: String
  for +hash: String
  {FP.fetch.ask(L.Member{path, entry}, here, hub, hash) == F.Tree{hash, entry} : F.Ask}

# LAW: and, once they are listed, it is the member walked from its entry over
# them
law fetch_member_walks:
  for +rs: List<&2, F.Reply>
  for +path: String
  for +entry: String
  for fs: List<&2, K.Item>
  for here: String
  for hub: String
  for +hash: String
  for ls: List<&2, W.Source>
  for eh: {F.heard(rs, F.Tree{hash, entry}) == F.Heard{F.Seen{W.Listed{ls}}} : F.Heard}
  {FP.part.fetch(rs, L.Member{path, entry}, fs, here, hub, hash)
    == FP.member.walked(K.of(entry, FP.files.of(ls)), fs, path, hash) : FP.Part}

# LAW: a walk that hashes to the hash the lock records arrives as the files it
# walked, which the lock's sums then judge as any tree's
law fetch_member_same:
  for +hash: String
  for root: String
  for wfs: List<&2, K.Source>
  for sums: List<&2, K.Item>
  for fs: List<&2, K.Item>
  for +path: String
  {FP.member.walked(K.Walked{hash, root, wfs, sums}, fs, path, hash) == FP.Got{FP.cand(fs, "", wfs)} : FP.Part}

# LAW: and one that hashes to any other is refused, naming the member
law fetch_member_moved:
  for +now: String
  for root: String
  for wfs: List<&2, K.Source>
  for sums: List<&2, K.Item>
  for fs: List<&2, K.Item>
  for +path: String
  for +hash: String
  for en: {String.eq(now, hash) == False{} : Bool}
  {FP.member.walked(K.Walked{now, root, wfs, sums}, fs, path, hash)
    == FP.No{"ez: workspace member " ++ path ++ " is " ++ now ++ " in the committed files, and the lock records " ++
      hash ++ "; run ez lock"} : FP.Part}

# LAW: a package refused stops the fetch with its reason, so the fetch lays
# nothing (`fetch_refusal_writes_nothing`)
law fetch_member_stops:
  for fs: List<&2, K.Item>
  for hash: String
  for +why: String
  for vs: List<&2, FP.Verdict>
  {FP.outcome.of(FP.judge(fs, hash, FP.No{why}) <> vs) == P.Refused{why} : P.Outcome}
