# A place `ez add` resolved a target to, shown on one line: its kind first,
# `bad`, `local` or `remote`, then what it holds, a remote's url and slug in
# that order, each after one space. This is internal: it fixes the form a
# place is read back in by whoever compares one.
import Base
import ../src/ez/target.bend as T

# LAW: a bad target shows its reason
law show_bad:
  for why: String
  {T.show(T.Bad{why}) == "bad " ++ why : String}

# LAW: a local target shows its path
law show_local:
  for path: String
  {T.show(T.Local{path}) == "local " ++ path : String}

# LAW: a remote target shows its url, then its slug
law show_remote:
  for url: String
  for slug: String
  {T.show(T.Remote{url, slug}) == "remote " ++ url ++ " " ++ slug : String}
