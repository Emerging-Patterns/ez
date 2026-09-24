# fetch: the laws. The human states them; PROOF.bend must prove them. They
# are stated over the plan `ez fetch` runs (fetch/plan.bend) and the
# questions it asks (`FP.wants`), so what they say of the plan is what the
# command does, the interpreter's faithfulness being EZ-TRUST-2.
#
# `F.sects(w)` is the lock the World holds, as tables, and
# `FP.locked(ss, h)` the files it records under the hash `h`.
import Base
import ./world.bend as F
import ./plan.bend as FP
import ../lock/plan.bend as P
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../lock/lock.bend as L
import ../lock/up.bend as Up
import ../lock/world.bend as W
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path

# LAW: `ez fetch` that refuses writes, lays and removes nothing: no tree
# under BEND_LIB, not even one of a package that checked before the one that
# failed, and a tree already there is not removed. Its plan has no effect at
# all; the reason is how it ends.
# EZ-OUT-2
law fetch_refusal_writes_nothing:
  for +w: F.World
  for r: {FP.refuses(w) == True{} : Bool}
  {P.writes(FP.plan(w)) == False{} : Bool}

# LAW: `ez fetch` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
# EZ-OUT-1
law fetch_exits_as_it_refuses:
  for +w: F.World
  {P.code(FP.plan(w)) == P.status.of(FP.refuses(w)) : U32}

# LAW: with no ez.toml, `ez fetch` refuses, whatever the lock says
# EZ-LED-6
law fetch_needs_ledger:
  for +here: String
  for got: Maybe<&2, String>
  for rs: List<&2, F.Reply>
  {FP.refuses(F.World{here, False{}, got, rs}) == True{} : Bool}

# LAW: and asks nothing first
# EZ-LED-6
law fetch_needs_ledger_asks_nothing:
  for +here: String
  for got: Maybe<&2, String>
  for rs: List<&2, F.Reply>
  {FP.wants(F.World{here, False{}, got, rs}) == [] : List<&2, F.Ask>}

# LAW: with no ez.lock.toml, `ez fetch` refuses too, as `uv sync --frozen`
# does, rather than resolving one: a fetch writes no lock
law fetch_needs_lock:
  for +here: String
  for led: Bool
  for rs: List<&2, F.Reply>
  {FP.refuses(F.World{here, led, None{}, rs}) == True{} : Bool}

# LAW: and asks nothing first
law fetch_needs_lock_asks_nothing:
  for +here: String
  for led: Bool
  for rs: List<&2, F.Reply>
  {FP.wants(F.World{here, led, None{}, rs}) == [] : List<&2, F.Ask>}

# LAW: every tree `ez fetch` lays holds the files the lock records under the
# hash it is laid under, in the lock's order, each with a text whose digest
# is exactly the sum the lock records for it, whether it came from the hub or
# from a checkout. Equal digests are the strongest match: a hub body whose
# digest equals the lock's sum is one whose digest starts with it.
# EZ-FETCH-1
law fetch_lays_the_lock:
  for +w: F.World
  {FP.lays.locked(F.sects(w), FP.effects(FP.plan(w))) == True{} : Bool}

# LAW: every tree `ez fetch` lays has the manifest of the texts it lays as its
# last file, each weighed by its own text, and is named by that manifest's
# `0x` hash, so a lock that records files under a name they do not hash to
# lays nothing
# EZ-HASH-3
law fetch_lays_named:
  for +w: F.World
  {P.lays.named(FP.effects(FP.plan(w))) == True{} : Bool}

# LAW: every checkout `ez fetch` asks for is asked of the source the lock
# records for that package, anchored at the project: a URL and an absolute
# path as they are, and a relative path joined to the directory the project
# is in, wherever ez was run from
# EZ-LED-8
law fetch_asks_anchored:
  for +w: F.World
  {FP.asks.anchored(F.here(w), F.sects(w), FP.wants(w)) == True{} : Bool}

# LAW: and `ez fetch` writes no file, so the lock and ez.toml keep every
# source as it was recorded; it only lays trees
# EZ-LED-8
law fetch_keeps_records:
  for +w: F.World
  for +path: String
  {P.put.plan(FP.plan(w), path) == P.Kept{} : P.Wrote}

# LAW: every tree `ez fetch` lays for a git package comes from a checkout that
# weighed to the narHash the lock records for it, so a fetch pins the tree
# around the files it lays as well as their bytes, the tree nix rebuilds the
# package from. A hub package has no checkout, and a tree already under
# BEND_LIB that the lock's checks pass is kept and not fetched.
# EZ-FETCH-1
law fetch_lays_weighed:
  for +w: F.World
  {FP.lays.weighed(F.sects(w), F.replies(w), F.here(w), FP.effects(FP.plan(w))) == True{}
    : Bool}

# LAW: and what weighing to it is: the checkout of a git package passes
# exactly when the lock records a narHash for it and the checkout's is that
# one. A lock with none records nothing to check, so it is refused too.
# EZ-FETCH-1
law fetch_weighs_the_checkout:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +h: String
  for +url: String
  for +rev: String
  for entry: String
  for root: String
  for +nar: String
  for tag: String
  for +got: String
  for fs: List<&2, K.Source>
  for q: {L.pack.src(L.pack_of(ss, h)) == L.Git{url, rev, entry, root, nar, tag} : L.Src}
  for a: {F.heard(rs, F.Git{h, Up.Clone{Path.anchor(here, url), rev}})
    == F.Heard{F.Said{Up.Cloned{got, fs}}} : F.Heard}
  {String.is_empty(FP.weighed(ss, rs, here, h))
    == Bool.and(Bool.not(String.is_empty(nar)), String.eq(got, nar)) : Bool}

# LAW: a package whose checkout did not weigh to it refuses the fetch, with
# why, whatever files arrived. A refused fetch lays nothing
# (`fetch_refusal_writes_nothing`).
# EZ-FETCH-1
law fetch_refuses_unweighed:
  for +fs: List<&2, K.File>
  for +h: String
  for +why: String
  for ls: List<&2, W.Source>
  for n: {String.is_empty(why) == False{} : Bool}
  {FP.judge(fs, h, FP.weigh.part(why, FP.Got{ls})) == FP.Stop{why} : FP.Verdict}
