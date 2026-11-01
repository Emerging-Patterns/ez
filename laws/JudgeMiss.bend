import Base
import ../src/hub/hub.bend as Web

# LAW: a file:// that did not arrive is Miss, not Have of an empty body.
# The fetch's ok bit is False when the path is not there.
law judge_miss:
  for +good: Bool
  for +url: String
  for +body: String
  {Web.judge(False{}, good, url, body)
    == Web.Miss{url ++ ": " ++ body} : Web.Got}
