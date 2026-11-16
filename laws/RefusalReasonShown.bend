# What `ez check`, `ez build` and `ez run` say they refused for: the reason a
# refusal carries, exactly, and nothing for a command that started bend.
# This is internal: it fixes what ez/start.bend hands the interpreter to
# print.
import Base
import ../src/ez/start.bend as S

# LAW: a refusal says its own reason
law why_refused:
  for w: String
  {S.why(S.Refused{w}) == w : String}

# LAW: and a command that started bend says nothing
law why_started:
  for l: List<&2, String>
  {S.why(S.Starts{l}) == "" : String}
