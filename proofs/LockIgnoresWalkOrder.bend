# proofs of laws/LockIgnoresWalkOrder.bend
import Base
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../laws/LockIgnoresWalkOrder.bend as Laws
import ../laws/SortPerm.bend as L1
import ../laws/WalkKeepsHashesDistinct.bend as L2
import ../laws/defs/DistinctPackHashes.bend as D1
import ../laws/defs/LockInputs.bend as D2
import ../laws/defs/WorldAfterLock.bend as D3
import ./lemmas/DistinctWalkSteps.bend as M1
import ./lemmas/FileInsertOrder.bend as M2

# The order a lock is written in. The lock's text depends on its packages
# only through their blocks sorted by `K.file.sort`. A package list
# rearranged is its blocks rearranged the same way, and distinct hashes are
# distinct block paths, so pkg's `sort_perm` sorts either list's blocks into
# the same list.

# LAW: a package put at a place is its block put at the same place
law blocks_ins_at:
  for +n: Nat
  for +x: L.Pack
  for +ps: List<&2, L.Pack>
  {L.pack.blocks(Laws.packs.perm.ins_at(n, x, ps))
    == D2.files.perm.ins_at(n, L.pack.block(x), L.pack.blocks(ps)) : List<&2, K.Item>}

def blocks_ins_at(n, x, ps):
  match n ps:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
        bs => L.pack.block(h) <> bs,
        L.pack.blocks(Laws.packs.perm.ins_at(p, x, t)),
        D2.files.perm.ins_at(p, L.pack.block(x), L.pack.blocks(t)),
        blocks_ins_at(p, x, t))

# LAW: a package list rearranged is its blocks rearranged
law blocks_perm:
  for +ns: List<&2, Nat>
  for +ps: List<&2, L.Pack>
  {L.pack.blocks(Laws.packs.perm(ns, ps)) == D2.files.perm(ns, L.pack.blocks(ps))
    : List<&2, K.Item>}

def blocks_perm(ns, ps):
  match ns ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{h, t}:
      {==}
    case Con{n, ms} Nil{}:
      {==}
    case Con{+n, +ms} Con{+h, +t}:
      Equal.trans(List<&2, K.Item>,
        L.pack.blocks(Laws.packs.perm.ins_at(n, h, Laws.packs.perm(ms, t))),
        D2.files.perm.ins_at(n, L.pack.block(h), L.pack.blocks(Laws.packs.perm(ms, t))),
        D2.files.perm.ins_at(n, L.pack.block(h), D2.files.perm(ms, L.pack.blocks(t))),
        blocks_ins_at(n, h, Laws.packs.perm(ms, t)),
        Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
          bs => D2.files.perm.ins_at(n, L.pack.block(h), bs),
          L.pack.blocks(Laws.packs.perm(ms, t)), D2.files.perm(ms, L.pack.blocks(t)),
          blocks_perm(ms, t)))

# LAW: a hash no package of a list has is a path no block of it has, whatever
# the block's text
law fresh_blocks:
  for +x: String
  for +s: String
  for +ps: List<&2, L.Pack>
  {D1.hash.fresh(x, ps) == D2.file.fresh(K.Item{x, s}, L.pack.blocks(ps)) : Bool}

def fresh_blocks(x, s, ps):
  match ps:
    case []:
      {==}
    case L.Pack{+h, _src, _fs} <> +t:
      Equal.cong(Bool, Bool, b => Bool.and(Bool.not(String.eq(x, h)), b),
        D1.hash.fresh(x, t), D2.file.fresh(K.Item{x, s}, L.pack.blocks(t)),
        fresh_blocks(x, s, t))

# LAW: so distinct hashes are distinct block paths
law distinct_blocks:
  for +ps: List<&2, L.Pack>
  {D1.packs.distinct(ps) == D2.files.distinct(L.pack.blocks(ps)) : Bool}

def distinct_blocks(ps):
  match ps:
    case []:
      {==}
    case L.Pack{+h, +src, +fs} <> +t:
      Equal.trans(Bool,
        Bool.and(D1.hash.fresh(h, t), D1.packs.distinct(t)),
        Bool.and(D2.file.fresh(L.pack.block(L.Pack{h, src, fs}), L.pack.blocks(t)),
          D1.packs.distinct(t)),
        Bool.and(D2.file.fresh(L.pack.block(L.Pack{h, src, fs}), L.pack.blocks(t)),
          D2.files.distinct(L.pack.blocks(t))),
        Equal.cong(Bool, Bool, b => Bool.and(b, D1.packs.distinct(t)),
          D1.hash.fresh(h, t),
          D2.file.fresh(L.pack.block(L.Pack{h, src, fs}), L.pack.blocks(t)),
          fresh_blocks(h, T.render(L.pack.sects.of(h, src, K.files_of(fs))), t)),
        Equal.cong(Bool, Bool,
          b => Bool.and(D2.file.fresh(L.pack.block(L.Pack{h, src, fs}),
            L.pack.blocks(t)), b),
          D1.packs.distinct(t), D2.files.distinct(L.pack.blocks(t)), distinct_blocks(t)))

# LAW: the blocks of a rearranged list of distinct hashes sort to the blocks
# of the list, sorted
law blocks_sort_perm:
  for +ns: List<&2, Nat>
  for +ps: List<&2, L.Pack>
  for dis: {D1.packs.distinct(ps) == True{} : Bool}
  {K.file.sort(L.pack.blocks(Laws.packs.perm(ns, ps))) == K.file.sort(L.pack.blocks(ps))
    : List<&2, K.Item>}

def blocks_sort_perm(ns, ps, dis):
  Equal.trans(List<&2, K.Item>,
    K.file.sort(L.pack.blocks(Laws.packs.perm(ns, ps))),
    K.file.sort(D2.files.perm(ns, L.pack.blocks(ps))),
    K.file.sort(L.pack.blocks(ps)),
    Equal.cong(List<&2, K.Item>, List<&2, K.Item>, bs => K.file.sort(bs),
      L.pack.blocks(Laws.packs.perm(ns, ps)), D2.files.perm(ns, L.pack.blocks(ps)),
      blocks_perm(ns, ps)),
    L1.sort_perm(ns, L.pack.blocks(ps),
      Equal.trans(Bool, D2.files.distinct(L.pack.blocks(ps)), D1.packs.distinct(ps), True{},
        Equal.sym(Bool, D1.packs.distinct(ps), D2.files.distinct(L.pack.blocks(ps)),
          distinct_blocks(ps)),
        dis)))

# The text is the sorted blocks under the `[lock]` table and before the
# tools, so it follows.
def Laws.lock_order_free(ns, nms, ps, ts, hub, dis):
  Equal.cong(List<&2, K.Item>, String,
    bs => L.text.of(hub, bs, T.render.all(D3.tail(nms, ts))),
    K.file.sort(L.pack.blocks(Laws.packs.perm(ns, ps))), K.file.sort(L.pack.blocks(ps)),
    blocks_sort_perm(ns, ps, dis))

# A block renders its files sorted, so this is `sort_perm` under the block.
def Laws.pack_order_free(ns, hash, src, fs, dis):
  Equal.cong(List<&2, K.Item>, K.Item,
    ys => K.Item{hash, T.render(L.pack.sects.of(hash, src, K.dedup(ys)))},
    K.file.sort(D2.files.perm(ns, fs)), K.file.sort(fs), L1.sort_perm(ns, fs, dis))

# LAW: the walk from any listing, over any ledger and verdicts, resolves each
# hash once
law walk_of_distinct:
  for +led: M.Read
  for listing: W.Listing
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  {D1.packs.distinct(P.walk.packs(P.walk.of(led, listing, ns, js))) == True{} : Bool}

def walk_of_distinct(led, listing, ns, js):
  match listing:
    case W.Unlisted{why}:
      {==}
    case W.Listed{+fs}:
      L2.walk_keeps_hashes_distinct(
        P.walk.fuel(List.append(&2, String, P.roots(fs), L.name.hashes(ns, P.roots.named(fs))), ns, js),
        L.ledger.read(led), ns, js,
        P.Walk{List.append(&2, String, P.roots(fs), L.name.hashes(ns, P.roots.named(fs))),
          [], [], ""}, {==})

# The walk is the same for a plain lock and an upgrade; only the ledger, the
# listing and the verdicts it walks over differ.
def Laws.plain_lock_hashes_distinct(w):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      walk_of_distinct(Up.next.read(W.next(args, ledger, ups)),
        W.listing.of(W.next(args, ledger, ups), listing),
        P.table(Up.next.read(W.next(args, ledger, ups)), W.judged.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies))
