# An import whose first path segment holds `@` is a hub dependency and never a
# file of the project. A name bend would refuse is refused, in bend's words,
# before any package is hashed around it.
import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ./defs/LicenseGiven.bend as D1

# LAW: an import of a named hub package is a dependency, never a module of
# the package: the walk queues no file for it, whether or not the hub rules
# its name in
law named_is_no_module:
  for +dir: String
  for +nd: String
  for +spec: String
  for e: {True{} == K.is_named(spec) : Bool}
  {K.task_of(dir, nd, spec) == [] : List<&2, K.Task>}

# LAW: and a file that imports a name the hub rules out stops the walk,
# naming it, with the file still queued, as bend refuses to load the file:
# no package is hashed around an import bend would not load
law unnamed_stops:
  for +tree: K.Tree
  for +text: String
  for +file: String
  for +ns: String
  for eb: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for rest: List<&2, K.Task>
  for g: {True{} == D1.given(K.find(tree, K.beside(file))) : Bool}
  for n: {False{} == String.is_empty(K.unnamed(K.scan.mods(K.scan(text)))) : Bool}
  {K.visit.found(tree, text, file, ns, eb, seen, out, rest)
    == K.State{seen, out, K.Unnamed{K.unnamed(K.scan.mods(K.scan(text)))}, K.Task{file, ns} <> rest}
    : K.State}

# LAW: and such a walk is refused in bend's words
law unnamed_refused:
  for +entry: String
  for +nv: String
  for +out: List<&2, K.Hit>
  {K.made.go(K.Unnamed{nv}, entry, out)
    == K.Refused{"ez: " ++ nv ++ " is not a package as <name>@<version>: a-z, 0-9 and -, " ++
      "1 to 64 characters, at four numbers like 1.0.0.0"} : K.Walked}

# LAW: the lock reads a named import as the package its name names, never as
# a module of the project, whether or not the hub rules the name in
law lock_reads_named:
  for +spec: String
  for e: {False{} == String.is_empty(K.named.of(spec)) : Bool}
  {L.named.put(spec) == [K.named.of(spec)] : List<&2, String>}
