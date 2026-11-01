# The NAR serialization of a directory does not depend on the order its
# entries are listed in.
import Base
import ../src/pkg/pkg.bend as K
import ../src/sha/nar.bend as Nar
import ./defs/LockInputs.bend as D1

# LAW: a directory's NAR is the same bytes whatever order its entries were
# listed in, so long as no name is listed twice, which a directory never does.
# `find` lists a directory in whatever order the filesystem keeps it, and two
# machines may keep it differently; this is why their narHash still agrees.
# `perm` and `distinct` are pkg's: an entry is a `K.Item` holding its name and
# its node's serial, so a rearranged directory is a rearranged file list.
# Every directory the walk serializes goes through `Nar.dir`, children and
# root alike, so the law at one level is the law for the whole tree.
law nar_dir_order_free:
  for +ns: List<&2, Nat>
  for +es: List<&2, K.Item>
  for +dis: {D1.files.distinct(es) == True{} : Bool}
  {Nar.dir(D1.files.perm(ns, es)) == Nar.dir(es) : String}
