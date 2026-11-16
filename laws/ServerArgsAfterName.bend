# How a test server reads its command line (src/check/argv.bend). This is
# internal to the test servers. `IO.args()` answers the program's own name
# first, as C's argv does, and then its arguments; a server's arguments are
# the ones after the name, in order, every one kept.
import Base
import ../src/check/argv.bend as A

# LAW: the program's name is dropped and its first argument comes first
law args_after_name:
  for name: String
  for first: String
  for rest: List<&1, String>
  {A.args(Con{name, Con{first, rest}}) == first <> A.copy(rest) : List<&2, String>}

# LAW: a command line that is only the name has no arguments
law args_name_only:
  for name: String
  {A.args(Con{name, Nil{}}) == [] : List<&2, String>}

# LAW: the copy keeps every argument, in order
law copy_keeps:
  for first: String
  for rest: List<&1, String>
  {A.copy(Con{first, rest}) == first <> A.copy(rest) : List<&2, String>}
