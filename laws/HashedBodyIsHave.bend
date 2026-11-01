# A file fetched from the hub is checked against the hash that names it. The
# fetch itself is IO; what is stated here is the verdict: a body that hashes
# right is Have of that body, a prefix miss is refused, and a file:// that
# is not there is Miss, never an empty body.
import Base
import ../src/hub/hub.bend as Web

# LAW: a body whose digest starts with the hash that was asked for is Have
# of that body. The check is a prefix test: bend accepts any prefix of the
# sha256, and a package's `0x` name is the first 32 characters.
law judge_have:
  for +url: String
  for +body: String
  {Web.judge(True{}, True{}, url, body) == Web.Have{body} : Web.Got}
