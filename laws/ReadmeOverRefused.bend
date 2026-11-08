import Base
import ../src/pkg/pkg.bend as K

# LAW: a README beside the entry over 65536 bytes, counted in the UTF-8 bytes
# its sha256 is taken over, refuses the package, naming it, as bend refuses
# to publish it
law readme_over_refused:
  for +tree: K.Tree
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  for text: String
  for here: {K.Here{text} == K.find(tree, K.readme(entry)) : K.Look}
  for over: {True{} == K.readme.over(text) : Bool}
  {K.made.all(tree, entry, K.State{seen, out, K.Going{}, queue})
    == K.Refused{"ez: " ++ K.readme(entry) ++ " cannot be published: it is over 65536 bytes, the most BendHub takes"}
    : K.Walked}
