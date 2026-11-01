import Base
import ../src/pkg/pkg.bend as K

# LAW: a module or entry that climbs above the checkout's top is refused,
# naming the import, wherever in the walk it is reached and whatever the walk
# was given. The walk never reads it: a package that reached it would be named
# after the directories above the checkout, which differ from machine to
# machine.
law escaping_import_refused:
  for f: Nat
  for +entry: String
  for +tree: K.Tree
  for +eb: String
  for +seen: List<&2, String>
  for +out: List<&2, K.Hit>
  for +file: String
  for +ns: String
  for +rest: List<&2, K.Task>
  for fresh: {False{} == K.seen.has(seen, file) : Bool}
  for up: {True{} == K.outside(file) : Bool}
  {K.made(entry, K.walk((1n + f : Nat), tree, eb,
      K.State{seen, out, K.Going{}, K.Task{file, ns} <> rest}))
    == K.Refused{"ez: the import " ++ K.climbs.name(ns, file)
      ++ " climbs out of the checkout"} : K.Walked}
