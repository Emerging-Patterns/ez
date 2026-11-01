import Base
import ../src/pkg/pkg.bend as K
import ./defs/LockInputs.bend as D1

# LAW: sorting a rearranged file list gives the list sorting gave already, so
# long as no path is named twice. The order a walk found the files in is one
# rearrangement of any other, so what `file.sort` answers is the walk's
# business and not the file system's.
law sort_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, K.Item>
  for +dis: {D1.files.distinct(xs) == True{} : Bool}
  {K.file.sort(D1.files.perm(ns, xs)) == K.file.sort(xs) : List<&2, K.Item>}
