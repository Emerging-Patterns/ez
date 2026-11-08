import Base
import ../src/pkg/pkg.bend as K

# LAW: a walk that went to its end without being given whether its entry has
# a README beside it asks for it, so no package is hashed without a README it
# may hold
law readme_asked:
  for +tree: K.Tree
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  for unasked: {K.Unasked{} == K.find(tree, K.readme(entry)) : K.Look}
  {K.made.all(tree, entry, K.State{seen, out, K.Going{}, queue})
    == K.Asks{K.readme(entry)} : K.Walked}
