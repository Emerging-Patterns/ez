# hub: the laws. The human states them; PROOF.bend must prove them. A file
# fetched from the hub is checked against the hash that names it. The fetch
# itself is IO; what is stated here is the verdict: a body that hashes right
# is Have of that body, a prefix miss is refused, and a file:// that is not
# there is Miss, never an empty body.
import Base
import ./hub.bend as Hub

# LAW: a body whose digest starts with the hash that was asked for is Have
# of that body. The check is a prefix test: bend accepts any prefix of the
# sha256, and a package's `0x` name is the first 32 characters.
law judge_have:
  for +url: String
  for +body: String
  {Hub.judge(True{}, True{}, url, body) == Hub.Have{body} : Hub.Got}

# LAW: a body whose digest does not start with the hash is refused. The
# reason names the url and says it does not hash to what was asked for.
law judge_refuse:
  for +url: String
  for +body: String
  {Hub.judge(True{}, False{}, url, body)
    == Hub.Miss{url ++ " does not hash to what was asked for"} : Hub.Got}

# LAW: a file:// that did not arrive is Miss, not Have of an empty body.
# The fetch's ok bit is False when the path is not there.
law judge_miss:
  for +good: Bool
  for +url: String
  for +body: String
  {Hub.judge(False{}, good, url, body)
    == Hub.Miss{url ++ ": " ++ body} : Hub.Got}

# LAW: the fixture manifest hashes to the prefix a package name is cut from.
law hash_match:
  {Hub.matches("182e9ab84416d28eef11e51eb5680c5e",
    "a8a411ce45f88c9659785973fe3416c2e8ae69584151db03f5997ce3eaff9a80 src/lib.bend\n")
    == True{} : Bool}

# LAW: a prefix the digest does not start with is not a match.
law hash_refuse:
  {Hub.matches("0000000000000000000000000000dead",
    "a8a411ce45f88c9659785973fe3416c2e8ae69584151db03f5997ce3eaff9a80 src/lib.bend\n")
    == False{} : Bool}
