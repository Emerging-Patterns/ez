import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path

# What a package holds besides its sources. bend 2.0.27 takes along every
# file named exactly `LICENSE` beside a file it publishes, at the same path in
# the package, and hashes it with the rest; it refuses a file under a
# directory named license in any case. That ez's walk and bend's publish agree
# is trusted in src/pkg/pkg.bend; these laws say what ez's side of it is.

# LAW: a file whose directory holds a LICENSE publishes it beside the file,
# at the file's own directory in the package
law license_goes_along:
  for +tree: K.Tree
  for +sc: K.Scan
  for +text: String
  for +file: String
  for +ns: String
  for +eb: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for rest: List<&2, K.Task>
  for lic: String
  for here: {K.Here{lic} == K.find(tree, K.beside(file)) : K.Look}
  {K.visit.put(K.Going{}, tree, sc, text, file, ns, eb, seen, out, rest)
    == K.State{file <> seen,
      K.Hit{K.raw_of(ns, eb), text} <> K.Hit{K.beside(K.raw_of(ns, eb)), lic}
        <> List.append(&2, K.Hit,
          K.foreigns(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(sc)), out),
      K.Going{},
      List.append(&2, K.Task, K.tasks(Path.dir(file), K.nsdir(ns), K.scan.mods(sc)), rest)}
    : K.State}
