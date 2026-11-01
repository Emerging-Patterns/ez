import Base
import ../src/pkg/path.bend as Path
import ../src/git/git.bend as Git

# LAW: when the entry sits at the same depth as the checkout root, the
# recorded root is a climb of nothing off the entry's own directory.
law root_rel_here:
  for +at: String
  for +root: String
  for +entry: String
  for e: {Nat.is_eq(Git.depth(Path.dir(at)), Git.depth(root)) == True{} : Bool}
  {Git.root.rel(at, root, entry) == Path.climb(0n, Path.dir(entry)) : String}
