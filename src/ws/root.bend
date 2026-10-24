# ws/root: which workspace a command run in a directory belongs to
# (EZ-WS-2). ez reads ez.toml from the directory it runs in; in a workspace
# that directory may be a member, so a command first finds its root: the
# nearest directory at or above it, up to the top of the git checkout, whose
# ledger is a workspace root that makes it a member. With none, the
# directory is a project of its own, as it always was. The design is
# docs/rfc/ez-workspaces.md.
#
# Both halves are pure. `asks` names the directories whose ez.toml the
# interpreter reads, each with the path from it down to where ez runs, nearest
# first; `root.go` decides from what was read, in that order. A path is its
# segments, relative to the top of the checkout, as `git rev-parse
# --show-prefix` prints it (`here.of`).
import Base
import ./workspace.bend as W

# a directory at or above where ez runs: its path from the top of the
# checkout, and the path from it down to where ez runs
type Ask is Data:
  Ask{dir: List<&2, String>, rel: List<&2, String>}

# one such directory, read: its ez.toml's text, or None when it has none
type Up is Data:
  Up{dir: List<&2, String>, rel: List<&2, String>, text: Maybe<&2, String>}

# where a command run in a directory stands: in a project of its own, in a
# workspace at `root` as the member `rel` below it (`[]` for the root itself),
# or nowhere, because a workspace table above it could not be read
type Found is Data:
  Alone{}
  Within{root: List<&2, String>, rel: List<&2, String>}
  Broken{why: String}

# where ez runs, from what `git rev-parse --show-prefix` printed: the
# segments before the `/` it ends with, none at the top. Anything else is no
# answer.
def here.of(+prefix: String) -> Maybe<&2, List<&2, String>>:
  W.cut(W.segs.of(prefix), "")

# every directory asked about from one segment further down, now one segment
# further from the top
def asks.under(+hd: String, xs: List<&2, Ask>) -> List<&2, Ask>:
  match xs:
    case []:
      []
    case Ask{ds, rs} <> tl:
      Ask{hd <> ds, rs} <> asks.under(hd, tl)

# the directories whose ez.toml is read: where ez runs, then each directory
# above it in turn, ending at the top of the checkout
def asks(here: List<&2, String>) -> List<&2, Ask>:
  match here:
    case []:
      [Ask{[], []}]
    case +hd <> +tl:
      List.append(&2, Ask, asks.under(hd, asks(tl)), [Ask{[], hd <> tl}])

# whether a workspace root makes the directory this far below it a member:
# the root itself always, and any other when an entry names it and no
# exclusion does
def claims(+spec: W.Spec, rel: List<&2, String>) -> Bool:
  match rel:
    case []:
      True{}
    case +hd <> +tl:
      W.chosen(spec, hd <> tl)

# a workspace root claims the directory, so the search ends there, or does
# not, and goes on above it
def root.claim(hit: Bool, +dir: List<&2, String>, +rel: List<&2, String>, rest: Found) -> Found:
  match hit:
    case True{}:
      Within{dir, rel}
    case False{}:
      rest

# what one directory's ledger says, against what the directories above it
# decided
def root.read(rd: W.Read, +dir: List<&2, String>, +rel: List<&2, String>, rest: Found) -> Found:
  match rd:
    case W.Lone{}:
      rest
    case W.Bad{why}:
      Broken{why}
    case W.Root{+spec}:
      root.claim(claims(spec, rel), dir, rel, rest)

# one directory, with or without a ledger
def root.at(text: Maybe<&2, String>, +dir: List<&2, String>, +rel: List<&2, String>, rest: Found) -> Found:
  match text:
    case None{}:
      rest
    case Some{tt}:
      root.read(W.spec.of(tt), dir, rel, rest)

# the root, from the directories read, nearest first: the first whose ledger
# is a workspace root that claims where ez runs, a table that could not be
# read if one comes first, and a project of its own when there is neither
def root.go(ups: List<&2, Up>) -> Found:
  match ups:
    case []:
      Alone{}
    case Up{ds, rs, tx} <> tl:
      rest = root.go(tl)
      root.at(tx, ds, rs, rest)
