# ws/hop: where a whole-workspace command runs (EZ-WS-2). `ez lock`, `ez
# fetch` and `ez doctor` act on the whole workspace from any member, so run in
# a member they run again at the root, with the same words, and end as that
# run ends. Run at the root, or in a project of its own, they run where they
# are. Which of the three it is, and the line that runs again, are decided
# here; ws/run.bend only reads what the search needs and runs what this says.
import Base
import ../pkg/path.bend as P
import ./workspace.bend as W
import ./root.bend as R

# where a command runs: where it is, again at the root's directory, or
# nowhere, because the search for the root was refused
type Hop is Data:
  Here{}
  Hop{dir: String}
  Stop{why: String}

# the root a member found, once it is known whether that is where ez runs
def hop.within(+top: String, root: List<&2, String>, rel: List<&2, String>) -> Hop:
  match rel:
    case []:
      Here{}
    case _hd <> _tl:
      Hop{P.join(top, W.segs.text(root))}

# where a command runs, from what the search found. `top` is the top of the
# checkout, as git printed it.
def hop(+top: String, found: R.Found) -> Hop:
  match found:
    case R.Alone{}:
      Here{}
    case R.Within{root, rel}:
      hop.within(top, root, rel)
    case R.Broken{why}:
      Stop{why}

# the program as it was started, found again from another directory: a path
# with a `/` in it taken from where ez was started, and a bare name looked up
# on PATH as it was
def program(+pwd: String, +prog: String) -> String:
  Bool.pick(String, String.contains(prog, "/"), P.anchor(pwd, prog), prog)

# the line that runs the same command at the root: a shell that changes to the
# root's directory and hands every word on as it was, with no word read by the
# shell, which takes them as its positional parameters
def line(+dir: String, +pwd: String, +prog: String, words: List<&2, String>) -> List<&2, String>:
  List.append(&2, String,
    ["sh", "-c", "cd -- \"$1\" && shift && exec \"$@\"", "sh", dir, program(pwd, prog)], words)

# ---------------------------------------------------------------------------
# the library a member's own command uses

# the BEND_LIB a command run in a member uses: the one the environment sets,
# or, when it sets none, the root's `.ez/lib`, where the workspace's lock lays
# its packages
type Lib is Data:
  Keep{}
  Set{lib: String}

# the root a member found, once it is known whether that is where ez runs
def lib.within(+top: String, root: List<&2, String>, rel: List<&2, String>) -> Lib:
  match rel:
    case []:
      Keep{}
    case _hd <> _tl:
      Set{P.join(P.join(top, W.segs.text(root)), ".ez/lib")}

# the library, once it is known whether the environment sets one
def lib.found(set: Bool, +top: String, found: R.Found) -> Lib:
  match set:
    case True{}:
      Keep{}
    case False{}:
      match found:
        case R.Alone{}:
          Keep{}
        case R.Within{root, rel}:
          lib.within(top, root, rel)
        case R.Broken{_why}:
          Keep{}

# the library a member's own command uses: `env` is BEND_LIB as the
# environment has it, "" for unset
def lib(+top: String, found: R.Found, +env: String) -> Lib:
  lib.found(Bool.not(String.is_empty(env)), top, found)

# the line that runs the same command where it is, with BEND_LIB set
def lib.line(+lib: String, +pwd: String, +prog: String, words: List<&2, String>) -> List<&2, String>:
  List.append(&2, String,
    ["sh", "-c", "BEND_LIB=\"$1\"; export BEND_LIB; shift; exec \"$@\"", "sh", lib, program(pwd, prog)], words)

# ---------------------------------------------------------------------------
# the lock a member's own command reads

# the root a member found, once it is known whether that is where ez runs
def lock.within(+top: String, root: List<&2, String>, rel: List<&2, String>) -> String:
  match rel:
    case []:
      "ez.lock.toml"
    case _hd <> _tl:
      P.join(P.join(top, W.segs.text(root)), "ez.lock.toml")

# the lock a command run in a directory reads: the root's, which is the only
# one a workspace has, or its own in a project of its own and at the root
def lock(+top: String, found: R.Found) -> String:
  match found:
    case R.Alone{}:
      "ez.lock.toml"
    case R.Within{root, rel}:
      lock.within(top, root, rel)
    case R.Broken{_why}:
      "ez.lock.toml"
