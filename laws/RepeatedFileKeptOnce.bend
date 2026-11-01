import Base
import ../src/pkg/pkg.bend as K

# LAW: a file set that names the same file twice in a row holds it once, so
# the manifest a repeated file produces is the manifest without the repeat.
# This is the half of the canonical form that dedup owns; the other half, that
# the order files were found in does not matter, is the three laws at the foot
# of this file. It moved here from Base's List.sort, which no proof could
# reach, and what it wanted was a permutation lemma over file.ins.
law dedup_dup:
  for +f: K.Item
  for t: List<&2, K.Item>
  {K.dedup(f <> (f <> t)) == K.dedup(f <> t) : List<&2, K.Item>}
