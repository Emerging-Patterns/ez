# pkg: the laws. The human states them; PROOF.bend must prove them. A package
# is named by the sha256 of its manifest, so the manifest is the identity: two
# file sets that name the same files must render the same text, or the hash ez
# computes is not the hash the hub serves.
import Base
import ./pkg.bend as P
import ./path.bend as Path

# a file put at a chosen place in a list: as many files pass in front of it as
# the number says, and it lands at the end when the list runs out first. This
# and `perm` below are the vocabulary the order-independence law needs and
# nothing else uses: ez never calls them, and they say here what a rearranged
# file list is in a form Bend can walk.
def perm.ins_at(n: Nat, x: P.File, xs: List<&2, P.File>) -> List<&2, P.File>:
  match n xs:
    case 0n _:
      x <> xs
    case 1n+p Nil{}:
      [x]
    case 1n+p Con{h, t}:
      h <> perm.ins_at(p, x, t)

# a list rearranged: each file is taken in turn and put back at the place its
# number names. This is what "the order the walk found them in" means here: a
# filesystem walk is one order and any other walk is another, and the numbers
# say how to get from the one to the other. The encoding is the Lehmer one, so
# the numbers reach every rearrangement of a list and nothing but its
# rearrangements — that is a fact about this encoding and is argued, not
# proved, since the laws below quantify over the numbers and never need it.
def perm(ns: List<&2, Nat>, xs: List<&2, P.File>) -> List<&2, P.File>:
  match ns xs:
    case Nil{} Nil{}:
      []
    case Nil{} Con{h, t}:
      h <> t
    case Con{n, ms} Nil{}:
      []
    case Con{n, ms} Con{h, t}:
      perm.ins_at(n, h, perm(ms, t))

# whether a file's path is none of the paths a list holds
def fresh(+x: P.File, xs: List<&2, P.File>) -> Bool:
  match xs:
    case []:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(String.eq(P.file.at(x), P.file.at(h))), fresh(x, t))

# whether a list names each path at most once. A package's file set does: a
# path is a file's identity here, and the walk reads a file once. Two entries
# of the same path but different sha256s are not a package, and the laws below
# say nothing about such a list, because there is nothing true to say: `dedup`
# keeps the last of a run, so which of the two survives is the order's to
# decide.
def distinct(xs: List<&2, P.File>) -> Bool:
  match xs:
    case []:
      True{}
    case Con{+h, +t}:
      Bool.and(fresh(h, t), distinct(t))

# LAW: a file set that names the same file twice in a row holds it once, so
# the manifest a repeated file produces is the manifest without the repeat.
# This is the half of the canonical form that dedup owns; the other half, that
# the order files were found in does not matter, is the three laws at the foot
# of this file. It moved here from Base's List.sort, which no proof could
# reach, and what it wanted was a permutation lemma over file.ins.
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

# LAW: sorting a rearranged file list gives the list sorting gave already, so
# long as no path is named twice. The order a walk found the files in is one
# rearrangement of any other, so what `file.sort` answers is the walk's
# business and not the file system's.
law sort_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, P.File>
  for +dis: {distinct(xs) == True{} : Bool}
  {P.file.sort(perm(ns, xs)) == P.file.sort(xs) : List<&2, P.File>}

# LAW: and so the manifest a package renders is the same text whatever order
# its files were found in. `manifest_of` sorts before it renders, so this
# follows from the law above.
law manifest_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, P.File>
  for +dis: {distinct(xs) == True{} : Bool}
  {P.manifest_of(perm(ns, xs)) == P.manifest_of(xs) : String}

# LAW: and so the `0x` name a package is published under is the same name on
# every machine. This is what ez's content addressing rests on: a lock that
# pins `0x<hash>` pins the same files wherever it is read.
law hash_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, P.File>
  for +dis: {distinct(xs) == True{} : Bool}
  {P.hash_of(perm(ns, xs)) == P.hash_of(xs) : String}
