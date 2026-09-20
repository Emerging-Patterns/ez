# pkg: the laws. The human states them; PROOF.bend must prove them. A package
# is named by the sha256 of its manifest, so the manifest is the identity: two
# file sets that name the same files must render the same text, or the hash ez
# computes is not the hash the hub serves.
import Base
import ./pkg.bend as P
import ./path.bend as Path

# LAW: a file set that names the same file twice in a row holds it once, so
# the manifest a repeated file produces is the manifest without the repeat.
# This is the half of the canonical form that dedup owns; the other half, that
# the order files were found in does not matter, belongs to this package's own
# file.sort and is stated but not proved (see PROOF.bend). It moved here from
# Base's List.sort, which no proof could reach, so it is now reachable: what it
# wants is a permutation lemma over file.ins.
law dedup_dup:
  for +f: P.File
  for t: List<&2, P.File>
  {P.dedup(f <> (f <> t)) == P.dedup(f <> t) : List<&2, P.File>}

# LAW: a package that found a file publishes a file. Deduplication drops
# repeats and never the last of them.
law dedup_keeps:
  for +h: P.File
  for t: List<&2, P.File>
  {List.is_empty(&2, P.File, P.dedup(h <> t)) == False{} : Bool}

# LAW: the base of a path is its last component, whatever comes before it.
# The walk keeps the one it is carrying only when nothing follows.
law base_last:
  for ps: List<&2, String>
  for +x: String
  {Path.base.last(List.append(&2, String, ps, [x])) == x : String}
