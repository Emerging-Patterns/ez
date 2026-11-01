# proofs of laws/RepeatedFileKeptOnce.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../laws/RepeatedFileKeptOnce.bend as Laws

# LAW: one step of the deduplication, with the branch the pick takes given as
# a parameter and the equation that put it there given alongside, since a
# match may not scrutinise a computed value
law dedup_dup.arm:
  for +f: K.Item
  for b: K.Item
  for t: List<&2, K.Item>
  for bb: Bool
  for eb: {String.eq(K.file.at(f), K.file.at(b)) == bb : Bool}
  {K.dedup.head(f, K.dedup.pick(bb, f, b <> t)) == K.dedup.pick(bb, f, b <> t)
    : List<&2, K.Item>}

def dedup_dup.arm(f, b, t, bb, eb):
  match bb:
    case True{}:
      Equal.cong(Bool, List<&2, K.Item>, x => K.dedup.pick(x, f, b <> t),
        String.eq(K.file.at(f), K.file.at(b)), True{}, eb)
    case False{}:
      Equal.cong(Bool, List<&2, K.Item>,
        x => K.dedup.pick(x, f, f <> (b <> t)),
        String.eq(K.file.at(f), K.file.at(f)), True{},
        Eq.string_eq_self(K.file.at(f)))

# LAW: offering the same file to a deduplicated list twice changes nothing
law dedup_dup.head:
  for +f: K.Item
  for r: List<&2, K.Item>
  {K.dedup.head(f, K.dedup.head(f, r)) == K.dedup.head(f, r)
    : List<&2, K.Item>}

def dedup_dup.head(f, r):
  match r:
    case []:
      Equal.cong(Bool, List<&2, K.Item>, x => K.dedup.pick(x, f, [f]),
        String.eq(K.file.at(f), K.file.at(f)), True{},
        Eq.string_eq_self(K.file.at(f)))
    case +b <> t:
      dedup_dup.arm(f, b, t, String.eq(K.file.at(f), K.file.at(b)), {==})

def Laws.dedup_dup(f, t):
  dedup_dup.head(f, K.dedup(t))
