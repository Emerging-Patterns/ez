import Base
import ../src/hub/hub.bend as Web

# LAW: a body whose digest does not start with the hash is refused. The
# reason names the url and says it does not hash to what was asked for.
law judge_refuse:
  for +url: String
  for +body: String
  {Web.judge(True{}, False{}, url, body)
    == Web.Miss{url ++ " does not hash to what was asked for"} : Web.Got}
