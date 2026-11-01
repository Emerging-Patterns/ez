# proofs of laws/FoundFileIsPublished.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/FoundFileIsPublished.bend as Laws

# LAW: whichever branch the pick takes, what comes back is a file and a rest
law dedup_keeps.arm:
  for -f: K.Item
  for -b: K.Item
  for -t: List<&2, K.Item>
  for bb: Bool
  {List.is_empty(&2, K.Item, K.dedup.pick(bb, f, b <> t)) == False{} : Bool}

def dedup_keeps.arm(_f, _b, _t, bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a file offered to any deduplicated list comes back with it
law dedup_keeps.head:
  for +h: K.Item
  for r: List<&2, K.Item>
  {List.is_empty(&2, K.Item, K.dedup.head(h, r)) == False{} : Bool}

def dedup_keeps.head(h, r):
  match r:
    case []:
      {==}
    case +b <> t:
      dedup_keeps.arm(h, b, t, String.eq(K.file.at(h), K.file.at(b)))

def Laws.dedup_keeps(h, t):
  dedup_keeps.head(h, K.dedup(t))
