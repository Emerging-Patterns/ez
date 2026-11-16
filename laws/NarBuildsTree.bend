# The NAR walk builds the node nix's dumper would write for a tree, from the
# paths of its listing in the order `find` prints them, top first. This is
# internal: it holds src/sha/nar.bend's build in place, not an interface.
#
# A listing whose top is a file is that file's regular node, executable when
# its owner may execute it; one whose top is a symlink is a symlink node of
# its target; a directory with nothing in it is the empty directory's node;
# and a file listed inside the top directory is that directory's one entry,
# under its name, holding the file's node. When a directory closes, its node
# becomes an entry of the directory around it, under its name, and the walk
# goes on in that directory with the paths still to place. What this proves
# is the build over listings of those shapes and the close of a nested
# directory; that a deeper listing builds the tree nix's dumper would write
# rests on the same steps and is trusted in src/sha/nar.bend.
# also rests on: laws/NarIgnoresEntryOrder.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/sha/nar.bend as Nar

# LAW: a listing that is one regular file is that file's node
law nar_lone_file:
  for ex: Bool
  for name: String
  for at: String
  for body: String
  {Nar.tree([Nar.Ent{"f", ex, name, at, body}]) == Some{Nar.regular(ex, body)}
    : Maybe<&2, String>}

# LAW: a listing that is one symlink is a symlink node of its target
law nar_lone_symlink:
  for ex: Bool
  for name: String
  for at: String
  for target: String
  {Nar.tree([Nar.Ent{"l", ex, name, at, target}]) == Some{Nar.symlink(target)}
    : Maybe<&2, String>}

# LAW: a directory with nothing under it is the empty directory's node
law nar_lone_directory:
  for ex: Bool
  for name: String
  for at: String
  for body: String
  {Nar.tree([Nar.Ent{"d", ex, name, at, body}]) == Some{Nar.empty()}
    : Maybe<&2, String>}

# LAW: a file listed inside the top directory is that directory's one entry,
# under its name, holding the file's node
law nar_file_in_directory:
  for dex: Bool
  for dname: String
  for dat: String
  for dbody: String
  for ex: Bool
  for +name: String
  for body: String
  {Nar.tree([Nar.Ent{"d", dex, dname, dat, dbody}, Nar.Ent{"f", ex, name, name, body}])
    == Some{Nar.dir([K.Item{name, Nar.regular(ex, body)}])} : Maybe<&2, String>}

# LAW: a directory that closes inside another becomes an entry of it, under
# its name, holding its node, and the walk goes on there with the paths still
# to place
law nar_close_nested:
  for at: String
  for name: String
  for kids: List<&2, K.Item>
  for pat: String
  for pname: String
  for pkids: List<&2, K.Item>
  for up: List<&2, Nar.Frame>
  for es: List<&2, Nar.Ent>
  {Nar.close(Nar.Frame{at, name, kids}, Nar.Frame{pat, pname, pkids} <> up, es)
    == Nar.Next{Nar.State{es, Nar.Frame{pat, pname, K.Item{name, Nar.dir(kids)} <> pkids}, up}}
    : Nar.Move}
