# ez/args: what the `ez` script hands the binary through the environment, as a
# native Bend binary takes no arguments of its own. EZ_CMD is the subcommand,
# EZ_ARGS the rest, one a line.
import Base

# the non-empty strings
def nonempty(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = nonempty(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# a variable's text; unset, ""
def text_of(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# a variable's text, one line a value
def lines_of(name: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
    return nonempty(String.lines(text_of(r)))

# the arguments after the subcommand
def args() -> IO(List<&2, String>):
  lines_of("EZ_ARGS")

# the subcommand; unset, ""
def command() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("EZ_CMD")
    return text_of(r)

# the nth argument, or "" when it was not given. Both the list and the count
# are scrutinised together, so the walk needs no helper to branch through.
def at(xs: List<&2, String>, n: Nat) -> String:
  match xs n:
    case Nil{} _m:
      ""
    case Con{h, _t} 0n:
      h
    case Con{_h, t} 1n+p:
      at(t, p)
