# ez/args: the command line, as the binary itself receives it. `IO.args()` gives
# a compiled Bend binary every argument it was started with: the first is the
# subcommand and the rest are its own. The runtime keeps `--threads`, `--gpu`,
# `--gpu-build` and `--help` for itself and strips them wherever they appear;
# everything after a `--` reaches the program untouched, those four included.
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

# the arguments the process was started with. `IO.args()` answers a `&1` list
# and the rest of ez reads its arguments more than once, so the walk copies it.
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

# every argument, each one readable twice
def all() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    xs : List<&1, String> <- IO.args()
    return copy(xs)

# the first argument and the ones after it. The pair is returned rather than
# asked about twice, since a match cannot scrutinise a local binder.
def split(xs: List<&2, String>) -> String & List<&2, String>:
  match xs:
    case Nil{}:
      ("", Nil{})
    case Con{h, t}:
      (h, t)

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

# every word after the first, which is what `run` forwards to the entry
def rest(as: List<&2, String>) -> List<&2, String>:
  match as:
    case Nil{}:
      Nil{}
    case Con{_h, t}:
      t

# `n` words dropped. What remains when the list runs out first is nothing.
def drop(xs: List<&2, String>, n: Nat) -> List<&2, String>:
  match xs n:
    case Nil{} _m:
      Nil{}
    case Con{+h, +t} 0n:
      h <> t
    case Con{_h, t} 1n+p:
      drop(t, p)

# a leading `--` is the separator, not a word the program was given
def undash(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Bool.pick(List<&2, String>, String.eq(h, "--"), t, h <> t)

# the words `ez tool run` forwards: everything after the target, with one
# leading `--` taken off
def tool.rest(as: List<&2, String>) -> List<&2, String>:
  undash(drop(as, 3n))

# `tool run` with its target, and without the words the program is given.
# A missing target is left missing, so the parse can say so.
def tool.line(+t: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(t), ["tool", "run"],
    ["tool", "run", t])

# whether this line is `tool run`
def is.tool.run(+as: List<&2, String>) -> Bool:
  Bool.and(String.eq(at(as, 0n), "tool"), String.eq(at(as, 1n), "run"))

# `tool run` parsed as the command and its target; any other line as itself
def argv.tool(hit: Bool, +as: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      tool.line(at(as, 2n))
    case False{}:
      as

# `run` parsed as the command alone, so the words it forwards are not flags
def argv.run(hit: Bool, +as: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      ["run"]
    case False{}:
      argv.tool(is.tool.run(as), as)

# a `run` line and a `tool run` line are parsed without the words they
# forward. Every other line is parsed as it arrived.
def argv.of(+as: List<&2, String>) -> List<&2, String>:
  argv.run(String.eq(at(as, 0n), "run"), as)
