import Base
import ../src/pkg/pkg.bend as K

# LAW: a package with a file under a directory named license is refused,
# naming it, and nothing is weighed
law license_dir_refused:
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  for some: {False{} == String.is_empty(K.licensed(pre, out)) : Bool}
  {K.made.checked(root, pre, out)
    == K.Refused{"ez: " ++ K.licensed(pre, out)
      ++ " is in a directory named license, which clashes with a LICENSE file"}
    : K.Walked}
