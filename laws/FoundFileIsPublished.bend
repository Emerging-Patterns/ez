import Base
import ../src/pkg/pkg.bend as K

# LAW: a package that found a file publishes a file. Deduplication drops
# repeats and never the last of them.
law dedup_keeps:
  for +h: K.Item
  for t: List<&2, K.Item>
  {List.is_empty(&2, K.Item, K.dedup(h <> t)) == False{} : Bool}
