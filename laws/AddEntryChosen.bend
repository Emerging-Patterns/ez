# `ez add` with no entry uses the revision's `[package] entry`, then
# `[package] bin`, then `main.bend`, and refuses if that file is not in the
# revision. An add that succeeds prints the import line for that entry's path
# inside the package, the line `ez publish` prints. `ez add <name>@<version>`
# with no entry uses the package's `main.bend`, then its first top-level
# `.bend` file, and records none when it has neither; it refuses an entry
# given that the package does not hold, and prints the import line with the
# name in place of the hash.
#
# This guarantee's import line is proved over the plan `ez add` runs
# (`src/add/plan.bend`): an add that does not refuse ends what it says with
# `Git.import.line` of the hash its walk made and the entry's path inside
# the package, `K.inside` of the walk's root and the entry
# (`add_says_import`). `ez publish` prints the same function of the same
# two, so both commands name a package's entry where the hub serves it: by
# its name alone, or, for a package whose imports climb out of the entry's
# directory, under the directories the package re-rooted above it. `ez add
# <name>@<version>` prints the same function with the name in place of the
# hash, for the entry it records (`add_named_says_import`).
import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/git/git.bend as Git
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H

# The walk, which is a pure function of the files it is given. `ez add` will
# give it every file of a checkout; `pkg_of` gives it none and answers each
# file it asks for from disk, so both run this one walk.

# LAW: an entry a checkout does not hold is refused, and named, whatever
# else the checkout holds and however much fuel the walk has. With the
# checkout's files as the list, this is laws/AddEntryChosen.bend's refusal:
# an entry that is not in the revision is refused, never hashed as an empty
# package. An entry above the checkout's top is refused too, by the next
# law.
law absent_entry_refused:
  for f: Nat
  for +entry: String
  for +fs: List<&2, K.Source>
  for inside: {False{} == K.outside(entry) : Bool}
  for miss: {None{} == K.look(fs, entry) : Maybe<&2, String>}
  {K.of.fuel((1n + f : Nat), entry, fs)
    == K.Refused{"ez: " ++ entry ++ " is imported but not there"} : K.Walked}

# LAW: with no entry, the one walked and recorded is the checkout's
# `[package] entry`, else its `bin`, else `main.bend` (`Git.entry.maybe`)
law add_entry_default:
  for +w: A.World
  for none: {A.entry.arg(w) == "" : String}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.dep.entry(AP.added(w)) == Git.entry.maybe(K.look(AP.files(w), "ez.toml")) : String}

# LAW: an entry the checkout does not hold is refused, never hashed as an
# empty package
law add_entry_absent:
  for +w: A.World
  for miss: {None{} == K.look(AP.files(w), Path.norm(AP.entry(w))) : Maybe<&2, String>}
  {AP.refuses(w) == True{} : Bool}

# LAW: `ez add` that does not refuse ends what it says with the import line
# for the entry's path inside the package it walked, which is where the hub
# serves the entry: its name alone, or, when an import climbs out of its
# directory, the entry under the directories the package re-rooted above it.
# `Git.import.line` is the line `ez publish` prints for a package too.
law add_says_import:
  for +w: A.World
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.last(AP.plan(w)) == Git.import.line(AP.hash(w), AP.at(w)) : String}

# LAW: with no entry given, the one recorded is the package's `main.bend`,
# else its first top-level `.bend` file, else none
law add_named_entry_default:
  for +w: A.World
  for ne: {A.entry.arg(w) == "" : String}
  for nr: {A.ref(w) == "" : String}
  {M.dep.entry(H.added(w)) == H.entry.of(H.files(w)) : String}

# LAW: an entry given that the package does not hold is refused
law add_named_entry_absent:
  for +w: A.World
  for given: {String.is_empty(H.asked(w)) == False{} : Bool}
  for miss: {H.holds(H.files(w), Path.norm(H.asked(w))) == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: an add that does not refuse and records an entry ends what it says
# with the import line for that entry by name, the line `ez publish` prints
# with the name in place of the hash
law add_named_says_import:
  for +w: A.World
  for +ok: {H.refuses(w) == False{} : Bool}
  for some: {String.is_empty(M.dep.entry(H.added(w))) == False{} : Bool}
  {H.last(H.plan(w)) == Git.import.line(A.target(w), Path.norm(M.dep.entry(H.added(w))))
    : String}

# The entry `ez add` walks when none is given: the checkout's `[package]
# entry`, else its `bin`, else `main.bend` (`Git.entry.pick`, over the values
# its ez.toml gives, "" for one it does not).

# LAW: an entry the package names is the one taken
law entry_pick_entry:
  for +file: String
  for +binary: String
  for e: {False{} == String.is_empty(file) : Bool}
  {Git.entry.pick(file, binary) == file : String}

# LAW: with no entry, its bin
law entry_pick_bin:
  for +file: String
  for +binary: String
  for e0: {True{} == String.is_empty(file) : Bool}
  for e1: {False{} == String.is_empty(binary) : Bool}
  {Git.entry.pick(file, binary) == binary : String}

# LAW: with neither, `main.bend`
law entry_pick_main:
  for +file: String
  for +binary: String
  for e0: {True{} == String.is_empty(file) : Bool}
  for e1: {True{} == String.is_empty(binary) : Bool}
  {Git.entry.pick(file, binary) == "main.bend" : String}
