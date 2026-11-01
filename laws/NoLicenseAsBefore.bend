import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path

# LAW: and a file whose directory holds none is found as it was before bend
# took licenses along, so a package without a LICENSE keeps its hash
law no_license_as_before:
  for +tree: K.Tree
  for +sc: K.Scan
  for +text: String
  for +file: String
  for +ns: String
  for +eb: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for rest: List<&2, K.Task>
  for none: {K.Absent{} == K.find(tree, K.beside(file)) : K.Look}
  {K.visit.put(K.Going{}, tree, sc, text, file, ns, eb, seen, out, rest)
    == K.State{file <> seen,
      K.Hit{K.raw_of(ns, eb), text} <> List.append(&2, K.Hit,
        K.foreigns(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(sc)), out),
      K.Going{},
      List.append(&2, K.Task, K.tasks(Path.dir(file), K.nsdir(ns), K.scan.mods(sc)), rest)}
    : K.State}
