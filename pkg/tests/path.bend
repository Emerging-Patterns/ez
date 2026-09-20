# pkg/path: the lexical path arithmetic the import walk is built on
import Base
import ../path.bend as P
import ../../check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a leading dot goes away", P.norm("./util/math.bend"), "util/math.bend")
    Check.eq_str("an inner climb cancels", P.norm("src/../lib.bend"), "lib.bend")
    Check.eq_str("a climb past the start survives", P.norm("util/../../x.bend"), "../x.bend")
    Check.eq_str("two climbs stay two", P.norm("../../x"), "../../x")
    Check.eq_str("a path that cancels to nothing is here", P.norm("src/.."), ".")
    Check.eq_str("a rooted path stays rooted", P.norm("/a/b/../c"), "/a/c")
    Check.eq_str("the root cannot be climbed above", P.norm("/../a"), "/a")
    Check.eq_str("a directory is the path without its last component",
      P.dir("src/lib.bend"), "src")
    Check.eq_str("a file with no directory is here", P.dir("lib.bend"), ".")
    Check.eq_str("the last component", P.base("src/util/math.bend"), "math.bend")
    Check.eq_str("a path taken relative to a directory",
      P.join("src", "./util/m.bend"), "src/util/m.bend")
    Check.eq_str("a climb out of a directory", P.join("src/util", "../../x.bend"), "x.bend")
    Check.eq_str("nowhere in particular is where the path already is",
      P.join("", "lib.bend"), "lib.bend")
    Check.eq_str("the trailing components of a path", P.tail("/home/me/repo/src", 2n), "repo/src")
    Check.eq_str("fewer components than asked for is all of them", P.tail("src", 2n), "src")
    Check.eq_str("how many climbs a path holds", Nat.show(P.ups("../../x")), "2")
    Check.eq_str("a path with no climbs", Nat.show(P.ups("a/b")), "0")
    Check.eq_str("a module name drops its extension", P.unbend("util/math.bend"), "util/math")
    Check.eq_str("a directory climbed back off", P.climb(2n, "a/b/c"), "a")
    Check.eq_str("climbing nothing leaves the directory", P.climb(0n, "a/b"), "a/b")
    Check.eq_str("climbing past the start leaves a climb", P.climb(2n, "a"), "..")

#|ok a leading dot goes away
#|ok an inner climb cancels
#|ok a climb past the start survives
#|ok two climbs stay two
#|ok a path that cancels to nothing is here
#|ok a rooted path stays rooted
#|ok the root cannot be climbed above
#|ok a directory is the path without its last component
#|ok a file with no directory is here
#|ok the last component
#|ok a path taken relative to a directory
#|ok a climb out of a directory
#|ok nowhere in particular is where the path already is
#|ok the trailing components of a path
#|ok fewer components than asked for is all of them
#|ok how many climbs a path holds
#|ok a path with no climbs
#|ok a module name drops its extension
#|ok a directory climbed back off
#|ok climbing nothing leaves the directory
#|ok climbing past the start leaves a climb
