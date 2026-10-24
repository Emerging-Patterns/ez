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
