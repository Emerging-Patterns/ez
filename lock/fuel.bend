# lock/fuel: how many steps a package walk may take. An import graph deeper
# than this is refused. The checker builds this Nat while it checks the walk,
# so the cap is one it can hold.
import Base

def cap() -> Nat:
  8192n
