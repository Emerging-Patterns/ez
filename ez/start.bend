# ez/start: what `ez check`, `ez build` and `ez run` start, decided from the
# ledger they read and the words they were given. Each starts one bend on
# the entry the ledger names, or refuses and starts nothing when there is no
# ez.toml or it does not parse, as cargo refuses a directory with no
# Cargo.toml. The interpreter (`ez/cmd.bend`) reads ez.toml, puts the
# project's BEND_LIB in front of the line (`Env.line`), runs it and exits;
# that it does so faithfully is EZ-TRUST-2.
import Base
import ../manifest/manifest.bend as M
import ../ez/args.bend as Args

# which of the three commands is asking, with what it was told: where a
# build goes, and every word of the line for a run
type Ask is Data:
  Check{}
  Build{out: String}
  Run{as: List<&2, String>}

# what a command does: refuse with a reason, having started nothing, or start
# bend with this line
type Start is Data:
  Refused{why: String}
  Starts{line: List<&2, String>}

# what each command is for, in the words a refusal says it with
def does(ask: Ask) -> String:
  match ask:
    case Check{}:
      "ez check checks a project's entry"
    case Build{_out}:
      "ez build builds a project's entry"
    case Run{_as}:
      "ez run runs a project's entry"

# why a directory with no ez.toml is refused
def none(ask: Ask) -> String:
  "ez: no ez.toml here; " ++ does(ask) ++ ", and ez init makes one"

# the entry file a ledger names, or "main.bend" when it names none
def entry.or(+file: String) -> String:
  Bool.pick(String, String.is_empty(file), "main.bend", file)

# the entry file of a ledger that parsed
def entry(ledger: M.Manifest) -> String:
  M.Manifest{_n, e, _b, _h, _ds, _ts} = ledger
  entry.or(e)

# the name a ledger that parsed gives the package
def named(ledger: M.Manifest) -> String:
  M.Manifest{n, _e, _b, _h, _ds, _ts} = ledger
  n

# where a build lands when nothing said: `bin/<package name>.out`. The name
# and not the entry file, because the entry is where a program starts and the
# name is what it is called: a package named `bolt` with its entry at
# `bolt/main.bend` builds `bin/bolt.out` and not `bin/main.out`.
def build.named(+name: String) -> String:
  "bin/" ++ name ++ ".out"

# where a build lands: what was asked for, or the default
def build.out(+at: String, +name: String) -> String:
  Bool.pick(String, String.is_empty(at), build.named(name), at)

# the line each command starts bend with, over a ledger that parsed: the
# entry checked into `.ez/check.js` and never run, built to a native binary,
# or run with every word after `run` (EZ-TOOL-9)
def line(ask: Ask, +ledger: M.Manifest) -> List<&2, String>:
  match ask:
    case Check{}:
      ["bend", entry(ledger), "-o", ".ez/check.js"]
    case Build{+out}:
      ["bend", entry(ledger), "-o", build.out(out, named(ledger))]
    case Run{as}:
      Args.run.line(entry(ledger), as)

# what a command does with the ledger it read
def read(+ask: Ask, ledger: M.Read) -> Start:
  match ledger:
    case M.Bad{why}:
      Refused{"ez: " ++ M.show(M.Bad{why})}
    case M.Good{+m}:
      Starts{line(ask, m)}

# what a command does with ez.toml's text, None when there is none
def start(+ask: Ask, text: Maybe<&2, String>) -> Start:
  match text:
    case None{}:
      Refused{none(ask)}
    case Some{t}:
      read(ask, M.parse(t))

# the status `ez run` exits with, given the status of the program it started
# (EZ-OUT-1): 1 for a refusal, which started none, and the program's own
# status otherwise, as `cargo run` exits. `ez check` and `ez build` end on
# what bend printed instead (`ez/ends.bend`).
def code(start: Start, program: U32) -> U32:
  match start:
    case Refused{_why}:
      1
    case Starts{_line}:
      program

# why a command refused, or "" when it started bend
def why(start: Start) -> String:
  match start:
    case Refused{w}:
      w
    case Starts{_line}:
      ""
