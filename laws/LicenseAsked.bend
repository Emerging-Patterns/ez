import Base
import ../src/pkg/pkg.bend as K

# LAW: a file whose LICENSE the walk was not given stops the walk, asking for
# it, with the file still queued, so no package is hashed without a LICENSE
# it may hold
law license_asked:
  for +tree: K.Tree
  for +text: String
  for +file: String
  for +ns: String
  for eb: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for rest: List<&2, K.Task>
  for unasked: {K.Unasked{} == K.find(tree, K.beside(file)) : K.Look}
  {K.visit.found(tree, text, file, ns, eb, seen, out, rest)
    == K.State{seen, out, K.Asking{K.beside(file)}, K.Task{file, ns} <> rest}
    : K.State}
