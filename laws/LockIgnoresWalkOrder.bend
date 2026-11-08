# Packages are written in hash order and each package's files in path order,
# so the lock's text does not depend on the order the walk found them in.
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ./defs/DistinctPackHashes.bend as D1
import ./defs/LockInputs.bend as D2

# The order a lock is written in. pkg says what a rearranged file list is,
# with `perm` and `distinct`; these say the same of a package list, in the
# same shape, so that a package list rearranged is its blocks rearranged.
# Law vocabulary: ez never calls them.

# a package put at a chosen place in a list, as pkg's `perm.ins_at` puts a
# file
def packs.perm.ins_at(place: Nat, pack: L.Pack, ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match place ps:
    case 0n _:
      pack <> ps
    case 1n+p Nil{}:
      [pack]
    case 1n+p Con{h, t}:
      h <> packs.perm.ins_at(p, pack, t)

# a package list rearranged, as pkg's `perm` rearranges a file list: the
# numbers reach every order the walk could have found the packages in
def packs.perm(ns: List<&2, Nat>, ps: List<&2, L.Pack>) -> List<&2, L.Pack>:
  match ns ps:
    case Nil{} Nil{}:
      []
    case Nil{} Con{h, t}:
      h <> t
    case Con{n, ms} Nil{}:
      []
    case Con{n, ms} Con{h, t}:
      packs.perm.ins_at(n, h, packs.perm(ms, t))

# LAW: the lock's text does not depend on the order the packages were found
# in. Packages are written in hash order, so any rearrangement of a list that
# names each hash once writes the same bytes, tools and hub alike.
law lock_order_free:
  for +ns: List<&2, Nat>
  for +nms: List<&2, L.Name>
  for +ps: List<&2, L.Pack>
  for +ts: List<&2, M.Cli>
  for +hub: String
  for dis: {D1.packs.distinct(ps) == True{} : Bool}
  {L.render.names(nms, ts, hub, packs.perm(ns, ps)) == L.render.names(nms, ts, hub, ps) : String}

# LAW: and a package's block, the text the lock holds for it, does not depend
# on the order its files were found in. Files are written in path order, so
# any rearrangement of a file list that names each path once writes the same
# block. This is pkg's `sort_perm` under `pack.block`.
law pack_order_free:
  for +ns: List<&2, Nat>
  for +hash: String
  for +src: L.Src
  for +fs: List<&2, K.Item>
  for dis: {D2.files.distinct(fs) == True{} : Bool}
  {L.pack.block(L.Pack{hash, src, D2.files.perm(ns, fs)})
    == L.pack.block(L.Pack{hash, src, fs}) : K.Item}

# LAW: so every package list plain `ez lock` resolves, which is the list its
# lock renders, names each hash once. That is `lock_order_free`'s premise,
# so the lock ez writes does not depend on the order the walk found its
# packages in.
law plain_lock_hashes_distinct:
  for w: W.World
  {D1.packs.distinct(P.packs(w)) == True{} : Bool}
