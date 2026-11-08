import Base
import ../src/pkg/pkg.bend as K

# LAW: a walk that stopped, on a missing module, an import that climbs out,
# a question, spent fuel or a name the hub rules out, is judged as it
# stopped: the README changes no refusal and asks nothing ahead of the walk
law stopped_walk_takes_no_readme:
  for +tree: K.Tree
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for stop: K.Stop
  for queue: List<&2, K.Task>
  for stopped: {False{} == K.stop.going(stop) : Bool}
  {K.made.all(tree, entry, K.State{seen, out, stop, queue})
    == K.made(entry, K.State{seen, out, stop, queue}) : K.Walked}
