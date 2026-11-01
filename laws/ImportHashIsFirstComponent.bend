import Base
import ../src/lock/lock.bend as L
import ./defs/Slashless.bend as D1

# LAW: an import names the package before its first slash. The hash is
# the first component, and everything after the slash is the path
# inside the package.
law spec_hash:
  for +h: String
  for +rest: String
  for +e: {D1.slashless(h) == True{} : Bool}
  {L.spec.hash(String.append(h, SCon{'/', rest})) == h : String}
