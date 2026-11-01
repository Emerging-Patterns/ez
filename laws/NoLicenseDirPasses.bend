import Base
import ../src/pkg/pkg.bend as K

# LAW: and a package with none is placed and weighed as before
law license_dir_passes:
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  for none: {True{} == String.is_empty(K.licensed(pre, out)) : Bool}
  {K.made.checked(root, pre, out) == K.made.placed(root, pre, out) : K.Walked}
