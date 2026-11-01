import Base
import ../src/pkg/path.bend as Path
import ../src/git/git.bend as Git

# LAW: when the checkout root is one directory above the entry, the
# recorded root is one climb off the entry's directory.
law root_rel_up:
  for +at: String
  for +root: String
  for +entry: String
  for e: {Nat.is_eq(Git.depth(Path.dir(at)), 1n+Git.depth(root)) == True{} : Bool}
  {Git.root.rel(at, root, entry) == Path.climb(1n, Path.dir(entry)) : String}
