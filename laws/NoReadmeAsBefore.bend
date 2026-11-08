import Base
import ../src/pkg/pkg.bend as K

# LAW: and a walk whose entry has no README beside it is judged as it was
# before bend took the README along, so a package without one keeps its hash
law no_readme_as_before:
  for +tree: K.Tree
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  for none: {K.Absent{} == K.find(tree, K.readme(entry)) : K.Look}
  {K.made.all(tree, entry, K.State{seen, out, K.Going{}, queue})
    == K.made(entry, K.State{seen, out, K.Going{}, queue}) : K.Walked}
