# pkg: the laws. The human states them; PROOF.bend must prove them. A package
# is named by the sha256 of its manifest, so the manifest is the identity: two
# file sets that name the same files must render the same text, or the hash ez
# computes is not the hash the hub serves.
import Base
import ./pkg.bend as P
import ./path.bend as Path
import ../sha/sha.bend as Sha

# a file put at a chosen place in a list: as many files pass in front of it as
# the number says, and it lands at the end when the list runs out first. This
# and `perm` below are the vocabulary the order-independence law needs and
# nothing else uses: ez never calls them, and they say here what a rearranged
# file list is in a form Bend can walk.
def perm.ins_at(place: Nat, file: P.File, xs: List<&2, P.File>) -> List<&2, P.File>:
  match place xs:
    case 0n _:
      file <> xs
    case 1n+p Nil{}:
      [file]
    case 1n+p Con{h, t}:
      h <> perm.ins_at(p, file, t)

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
def fresh(+file: P.File, xs: List<&2, P.File>) -> Bool:
  match xs:
    case []:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(String.eq(P.file.at(file), P.file.at(h))), fresh(file, t))

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
# EZ-HASH-1
law hash_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, P.File>
  for +dis: {distinct(xs) == True{} : Bool}
  {P.hash_of(perm(ns, xs)) == P.hash_of(xs) : String}

# The path algebra, which is the other half of what a package's identity rests
# on: a module's name inside a package is the path it was reached through, and
# Base has no realpath, so `.` and `..` are resolved by text. A miscount there
# renames a module, and a renamed module is a different `0x` name.
#
# Two pieces of vocabulary the laws below need and nothing else uses. They
# say, in a form Bend can walk, what "this path holds no separator" means and
# which half of a half-finished normalisation is the root flag.

# whether a string holds no separator, and so is one component of a path
def slashless(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(Char.is_eq(h, '/')), slashless(t))

# whether a half-finished normalisation began at the root
def walk.abs(state: Path.Walk) -> Bool:
  Path.Walk{abs, out} = state
  abs

# LAW: a component that is none of the three the walk acts on is kept, text
# for text. This is what makes a module's name the path it was reached
# through: the normaliser rewrites `.` and `..` and copies everything else, so
# no component is ever silently folded, trimmed or cased.
law comp_name:
  for +c: String
  for e0: {False{} == String.is_empty(c) : Bool}
  for e1: {False{} == String.eq(c, ".") : Bool}
  for e2: {False{} == String.eq(c, "..") : Bool}
  {Path.comp_of(c) == Path.CName{c} : Path.Comp}

# LAW: a climb cancels the component it climbs off, whatever was kept before
# it and whether or not the path began at the root.
law up_cancels:
  for abs: Bool
  for +h: String
  for t: List<&2, String>
  for e: {False{} == String.eq(h, "..") : Bool}
  {Path.up(abs, h <> t) == t : List<&2, String>}

# LAW: and a climb past a climb cancels nothing, because a climb is not a
# component to climb off. Two `..` in a row stay two: this is the edge that
# decides how far `pkg.place` re-roots a package, and folding them would
# re-root it one directory too shallow.
law up_stacks:
  for abs: Bool
  for t: List<&2, String>
  {Path.up(abs, ".." <> t) == ".." <> (".." <> t) : List<&2, String>}

# LAW: a path with no separator in it splits into itself, one component. The
# two laws under it are read off this one.
law split_plain:
  for +p: String
  for +e: {slashless(p) == True{} : Bool}
  {String.split(p, '/') == [p] : List<&2, String>}

# LAW: so the base of a path with no separator is the path. The walk carries
# the one component it has, and nothing follows it.
law base_plain:
  for +p: String
  for e: {slashless(p) == True{} : Bool}
  {Path.base(p) == p : String}

# LAW: and asking for the last component of such a path, or for more
# components than it has, gives all of it rather than the empty string a bad
# `take` would give. It holds for every such path and every count.
law tail_plain:
  for +p: String
  for q: Nat
  for e: {slashless(p) == True{} : Bool}
  {Path.tail(p, 1n+q) == p : String}

# LAW: taking the directory of a path is joining a climb onto it. `dir` is
# written as a splice and `join` as a normalisation of a splice, and this
# holds the one to the other, so the climb `pkg.place` takes is a join.
law dir_is_climb:
  for +p: String
  for e: {False{} == String.is_empty(p) : Bool}
  {Path.dir(p) == Path.join(p, "..") : String}

# LAW: a leading climb is one climb more than what follows it. This is the
# count `pkg.place` re-roots by, so a path that climbs twice must count twice.
law ups_climb:
  for p: String
  {Path.ups("../" ++ p) == 1n+Path.ups(p) : Nat}

# LAW: a path that does not end in `.bend` is its own module name. The strip
# is a strip and never a truncation of five characters off whatever it was
# handed.
law unbend_plain:
  for +p: String
  for e: {False{} == String.ends_with(p, ".bend") : Bool}
  {Path.unbend(p) == p : String}

# LAW: a normalisation carries the root flag it started with, whatever the
# components did to what it kept.
law walk_keeps_root:
  for cs: List<&2, String>
  for +w: Path.Walk
  {walk.abs(Path.norm.walk(cs, w)) == walk.abs(w) : Bool}

# LAW: so a path that began at the root normalises to a path that begins at
# the root. A climb at the root goes nowhere, which is `up.root`, and this is
# that fact stated where it bites: no count of `..` walks a normalisation off
# the top of an absolute path.
law norm_absolute:
  for +p: String
  for e: {True{} == String.starts_with(p, "/") : Bool}
  {String.starts_with(Path.norm(p), "/") == True{} : Bool}

# LAW: and so re-rooting an absolute path leaves it absolute, however many
# directories it is climbed back off. `pkg.place` climbs by the deepest `..`
# any module of the package used, and this says that count cannot escape.
law climb_absolute:
  for n: Nat
  for +p: String
  for e: {True{} == String.starts_with(p, "/") : Bool}
  {String.starts_with(Path.climb(n, p), "/") == True{} : Bool}

# LAW: a `.` is not a component. The walk skips it, so `./` in a path is
# never a name a module is published under.
law comp_dot:
  {Path.comp_of(".") == Path.CSkip{} : Path.Comp}

# LAW: skipping a component leaves the walk as it was
law skip_id:
  for w: Path.Walk
  {Path.norm.go(w, Path.CSkip{}) == w : Path.Walk}

# LAW: so a leading `./` is the path without it, as long as the path did
# not already begin at the root. Gluing `./` onto a rooted path makes it
# relative, and that is a different path.
law norm_dot:
  for +p: String
  for e: {False{} == String.starts_with(p, "/") : Bool}
  {Path.norm("./" ++ p) == Path.norm(p) : String}

# LAW: the directory of a single real component is here. A file with no
# slash in its name sits in the current directory, so climbing it off
# leaves `.` and not the empty string a join would write.
law dir_plain:
  for +p: String
  for +e: {slashless(p) == True{} : Bool}
  for +e0: {False{} == String.is_empty(p) : Bool}
  for e1: {False{} == String.eq(p, ".") : Bool}
  for e2: {False{} == String.eq(p, "..") : Bool}
  {Path.dir(p) == "." : String}

# LAW: a path taken relative to nowhere is the path. An empty directory
# means the path is already where it should be, and `join` still
# normalises, so this is `norm` and not the raw text.
law join_bare:
  for +p: String
  {Path.join("", p) == Path.norm(p) : String}

# LAW: climbing nothing leaves the path as `norm` left it. `pkg.place`
# climbs by a count, and a count of zero is a no-op on the directory.
law climb_zero:
  for +p: String
  {Path.climb(0n, p) == Path.norm(p) : String}

# LAW: a module path that ends in `.bend` drops those five characters.
# The strip is the suffix and nothing else, so a name that merely holds
# those characters in the middle is left alone.
law unbend_ext:
  for +p: String
  {Path.unbend(p ++ ".bend") == p : String}

# LAW: a path that holds no separator and is not a climb has no climbs.
# `pkg.place` re-roots by this count, so a file named in place does not
# lift the package.
law ups_plain:
  for +p: String
  for e: {slashless(p) == True{} : Bool}
  for e2: {False{} == String.eq(p, "..") : Bool}
  {Path.ups(p) == 0n : Nat}

# LAW: the last component of a path is the tail of length one. `base` and
# `tail` are written differently and this holds the one to the other.
law tail_one:
  for +p: String
  {Path.tail(p, 1n) == Path.base(p) : String}

# The header scan, which is what a package's file set is gathered from:
# which lines of a source file are modules, which are foreign bodies, and
# when the header has ended. A late import followed as if it were still
# in the header is a file the package does not hold, and a hub import
# followed as if it were a module is a walk that leaves the package.

# LAW: a spec that does not open `0x` is not a hub import. A relative
# path is a module of this package.
law hub_needs_0x:
  for +s: String
  for e: {False{} == String.starts_with(s, "0x") : Bool}
  {P.is_hub(s) == False{} : Bool}

# LAW: and a spec that holds no `/` is not one either. A `0x` name has
# no directory of its own, so the first `/` ends it; without one there
# is no package to name.
law hub_needs_slash:
  for +s: String
  for e: {False{} == String.contains(s, "/") : Bool}
  {P.is_hub(s) == False{} : Bool}

# LAW: a `0x` name followed by a path is a hub import, whatever the
# hash and whatever the path. This is the one `is_hub` answers True
# for, and it is the one the walk does not follow.
law hub_named:
  for +h: String
  for +rest: String
  {P.is_hub(("0x" ++ h) ++ ("/" ++ rest)) == True{} : Bool}

# LAW: a module named after the header has ended is dropped. The walk
# does not follow it.
law late_mod:
  for spec: String
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {P.scan.mod(False{}, spec, mods, foreign)
    == P.Head{False{}, mods, foreign} : P.Head}

# LAW: a module named while the header is still open is kept
law header_mod:
  for spec: String
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {P.scan.mod(True{}, spec, mods, foreign)
    == P.Head{True{}, spec <> mods, foreign} : P.Head}

# LAW: a body line ends the header, whatever it had gathered
law body_ends:
  for head: Bool
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {P.scan.go(P.Head{head, mods, foreign}, P.SBody{})
    == P.Head{False{}, mods, foreign} : P.Head}

# LAW: a foreign body is gathered wherever it sits. It lives in a def's
# body, long after the header has ended, and the package still uploads
# it.
law foreign_keeps_head:
  for head: Bool
  for at: String
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {P.scan.go(P.Head{head, mods, foreign}, P.SForeign{at})
    == P.Head{head, mods, at <> foreign} : P.Head}

# LAW: the `0x` name a file set is published under is the first
# thirty-two hex characters of the manifest's digest. A lock that pins
# `0x<hash>` pins this prefix, and nothing else of the digest.
law hash_is_prefix:
  for xs: List<&2, P.File>
  {P.hash_of(xs) == "0x" ++ String.take(Sha.hex(P.manifest_of(xs)), 32n)
    : String}
