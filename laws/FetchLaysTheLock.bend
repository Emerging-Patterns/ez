# `ez fetch` writes a package file under `BEND_LIB` only when its digest
# matches the lock: a hub body's digest starts with the lock's sum, a git
# file's digest equals it, and a git package's checkout weighs to the narHash
# the lock records.
#
# This guarantee is proved over the plan `ez fetch` runs
# (`src/fetch/plan.bend`): every tree it lays holds the files the lock
# records under that hash, in the lock's order, each with a text whose
# digest equals the lock's sum for it (`fetch_lays_the_lock`). The law asks
# the same of a hub body and a git file, and a digest that equals the lock's
# sum starts with it, so it covers those halves of the row. A git package is
# laid only from a checkout that weighed to the narHash the lock records for
# it (`fetch_lays_weighed`), which is a lock that records one and a checkout
# whose narHash is that one (`fetch_weighs_the_checkout`); any other
# checkout stops the package with the reason (`fetch_refuses_unweighed`),
# and a stopped package refuses the fetch, which lays nothing
# (laws/RefusalWritesNothing.bend). So a fetch pins the tree around the
# bytes it lays, the tree nix rebuilds the package from, and not only the
# bytes. A tree already under BEND_LIB is checked file by file before it is
# kept, and one that fails is fetched again rather than trusted; it was not
# fetched, so it has no checkout to weigh. That the interpreter reads what
# the hub served and what the checkout holds, weighs the checkout as
# `Nar.path` does, and lays each text as the plan says, is trusted in
# src/ez/app.bend.
#
# `F.sects(w)` is the lock the World holds, as tables, and `FP.locked(ss,
# h)` the files it records under the hash `h`.
import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../src/toml/toml.bend as T
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# LAW: every tree `ez fetch` lays holds the files the lock records under the
# hash it is laid under, in the lock's order, each with a text whose digest
# is exactly the sum the lock records for it, whether it came from the hub or
# from a checkout. Equal digests are the strongest match: a hub body whose
# digest equals the lock's sum is one whose digest starts with it.
law fetch_lays_the_lock:
  for +w: F.World
  {FP.lays.locked(F.sects(w), FP.effects(FP.plan(w))) == True{} : Bool}

# LAW: every tree `ez fetch` lays for a git package comes from a checkout that
# weighed to the narHash the lock records for it, so a fetch pins the tree
# around the files it lays as well as their bytes, the tree nix rebuilds the
# package from. A hub package has no checkout, and a tree already under
# BEND_LIB that the lock's checks pass is kept and not fetched.
law fetch_lays_weighed:
  for +w: F.World
  {FP.lays.weighed(F.sects(w), F.replies(w), F.here(w), FP.effects(FP.plan(w))) == True{}
    : Bool}

# LAW: and what weighing to it is: the checkout of a git package passes
# exactly when the lock records a narHash for it and the checkout's is that
# one. A lock with none records nothing to check, so it is refused too.
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
law fetch_refuses_unweighed:
  for +fs: List<&2, K.Item>
  for +h: String
  for +why: String
  for ls: List<&2, W.Source>
  for n: {String.is_empty(why) == False{} : Bool}
  {FP.judge(fs, h, FP.weigh.part(why, FP.Got{ls})) == FP.Stop{why} : FP.Verdict}
