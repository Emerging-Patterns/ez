# A command run in a directory takes as its workspace root the nearest
# directory at or above it, up to the top of its git checkout, whose ledger is
# a workspace root that makes the directory a member, the root itself
# included. With none, the directory is a project of its own, as before. A
# `[workspace]` table that cannot be read, in the directory or above it and
# nearer than its root, is refused. `ez lock`, `ez fetch` and `ez doctor` act
# on the whole workspace from any member. `ez add`, `ez remove`, `ez check`,
# `ez build`, `ez run` and `ez publish` act on the member's own ledger and
# entry, with the root's BEND_LIB and lock.
#
# A command run in a directory finds its root by reading the ledger of each
# directory from there up to the top of the checkout, nearest first, and the
# first workspace root that claims the directory is its root.
import Base
import ../src/pkg/path.bend as Path
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/root.bend as RRoot
import ../src/ws/hop.bend as HHop
import ./defs/DirectorySplits.bend as D1
import ./defs/LockInputs.bend as D2
import ./defs/WorldAfterLock.bend as D3

# ---------------------------------------------------------------------------
# finding the root (laws/WorkspaceRootFound.bend)

# every directory asked about after the first, nearest first. Law
# vocabulary: ez never calls it.
def asks.rest(here: List<&2, String>) -> List<&2, RRoot.Ask>:
  match here:
    case []:
      []
    case +hd <> +tl:
      List.append(&2, RRoot.Ask, RRoot.asks.under(hd, asks.rest(tl)), [RRoot.Ask{[], hd <> tl}])

# every directory asked about before the top of the checkout
def asks.init(here: List<&2, String>) -> List<&2, RRoot.Ask>:
  match here:
    case []:
      []
    case +hd <> +tl:
      RRoot.asks.under(hd, RRoot.asks(tl))

# LAW: the first directory asked about is where ez runs, as its own root
# would be
law asks_nearest:
  for +here: List<&2, String>
  {RRoot.asks(here) == RRoot.Ask{here, []} <> asks.rest(here) : List<&2, RRoot.Ask>}

# LAW: and the last is the top of the checkout, from which ez runs the whole
# path down
law asks_top:
  for +here: List<&2, String>
  {RRoot.asks(here) == List.append(&2, RRoot.Ask, asks.init(here), [RRoot.Ask{[], here}]) : List<&2, RRoot.Ask>}

# LAW: every directory asked about is above where ez runs, by the path it is
# asked with
law asks_split:
  for +here: List<&2, String>
  {D1.splits(RRoot.asks(here), here) == True{} : Bool}

# LAW: a directory with no ez.toml is passed by
law root_skips_none:
  for ds: List<&2, String>
  for rs: List<&2, String>
  for ups: List<&2, RRoot.Up>
  {RRoot.root.go(RRoot.Up{ds, rs, None{}} <> ups) == RRoot.root.go(ups) : RRoot.Found}

# LAW: and so is one whose ledger has no `[workspace]` table
law root_skips_lone:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, RRoot.Up>
  for ev: {WWorkspace.spec.of(tt) == WWorkspace.Lone{} : WWorkspace.Read}
  {RRoot.root.go(RRoot.Up{ds, rs, Some{tt}} <> ups) == RRoot.root.go(ups) : RRoot.Found}

# LAW: a `[workspace]` table that could not be read stops the search, so a
# command never takes a directory for a project of its own because the table
# above it was broken
law root_bad_refuses:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, RRoot.Up>
  for +why: String
  for ev: {WWorkspace.spec.of(tt) == WWorkspace.Bad{why} : WWorkspace.Read}
  {RRoot.root.go(RRoot.Up{ds, rs, Some{tt}} <> ups) == RRoot.Broken{why} : RRoot.Found}

# LAW: a workspace root that claims where ez runs is its root, whatever is
# above it
law root_claims_it:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, RRoot.Up>
  for +spec: WWorkspace.Spec
  for ev: {WWorkspace.spec.of(tt) == WWorkspace.Root{spec} : WWorkspace.Read}
  for ec: {RRoot.claims(spec, rs) == True{} : Bool}
  {RRoot.root.go(RRoot.Up{ds, rs, Some{tt}} <> ups) == RRoot.Within{ds, rs} : RRoot.Found}

# LAW: and one that does not is passed by
law root_passes_by:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, RRoot.Up>
  for +spec: WWorkspace.Spec
  for ev: {WWorkspace.spec.of(tt) == WWorkspace.Root{spec} : WWorkspace.Read}
  for ec: {RRoot.claims(spec, rs) == False{} : Bool}
  {RRoot.root.go(RRoot.Up{ds, rs, Some{tt}} <> ups) == RRoot.root.go(ups) : RRoot.Found}

# LAW: with no workspace above it, a directory is a project of its own
law root_none:
  for ups: List<&2, RRoot.Up>
  for +ev: {D2.quiet(ups) == True{} : Bool}
  {RRoot.root.go(ups) == RRoot.Alone{} : RRoot.Found}

# LAW: a workspace root claims itself, whatever its members are
law claims_self:
  for +spec: WWorkspace.Spec
  {RRoot.claims(spec, []) == True{} : Bool}

# LAW: and claims a directory below it exactly when that directory is a
# member (laws/WorkspaceMembersChosen.bend)
law claims_member:
  for +spec: WWorkspace.Spec
  for +hd: String
  for +tl: List<&2, String>
  {RRoot.claims(spec, hd <> tl) == WWorkspace.chosen(spec, hd <> tl) : Bool}

# LAW: a command run in a project of its own runs where it is
law hop_alone:
  for top: String
  {HHop.hop(top, RRoot.Alone{}) == HHop.Here{} : HHop.Hop}

# LAW: and so does one run at its workspace's root
law hop_at_root:
  for top: String
  for root: List<&2, String>
  {HHop.hop(top, RRoot.Within{root, []}) == HHop.Here{} : HHop.Hop}

# LAW: one run in a member runs again at the root's directory
law hop_member:
  for +top: String
  for +root: List<&2, String>
  for hd: String
  for tl: List<&2, String>
  {HHop.hop(top, RRoot.Within{root, hd <> tl}) == HHop.Hop{Path.join(top, WWorkspace.segs.text(root))} : HHop.Hop}

# LAW: and one whose search was refused runs nowhere, saying why
law hop_broken:
  for top: String
  for +why: String
  {HHop.hop(top, RRoot.Broken{why}) == HHop.Stop{why} : HHop.Hop}

# LAW: the run at the root is handed every word the command was run with,
# unchanged and in order
law hop_keeps_words:
  for +dir: String
  for +pwd: String
  for +prog: String
  for +words: List<&2, String>
  {D3.past(6n, HHop.line(dir, pwd, prog, words)) == words : List<&2, String>}

# ---------------------------------------------------------------------------
# a member's own commands use the root's library (laws/WorkspaceRootFound.bend)

# LAW: a library the environment sets is kept, wherever ez runs
law lib_keeps_env:
  for top: String
  for found: RRoot.Found
  for +ch: Char
  for +tt: String
  {HHop.lib(top, found, SCon{ch, tt}) == HHop.Keep{} : HHop.Lib}

# LAW: with none set, a command run in a member uses the root's `.ez/lib`
law lib_member:
  for +top: String
  for +root: List<&2, String>
  for hd: String
  for tl: List<&2, String>
  {HHop.lib(top, RRoot.Within{root, hd <> tl}, "")
    == HHop.Set{Path.join(Path.join(top, WWorkspace.segs.text(root)), ".ez/lib")} : HHop.Lib}

# LAW: and one run at the root, or in a project of its own, uses its own, as
# it always did
law lib_own:
  for top: String
  for root: List<&2, String>
  {HHop.lib(top, RRoot.Within{root, []}, "") == HHop.Keep{} : HHop.Lib}

# LAW: in a project of its own too
law lib_alone:
  for top: String
  {HHop.lib(top, RRoot.Alone{}, "") == HHop.Keep{} : HHop.Lib}

# LAW: the run with the root's library is handed every word, unchanged and in
# order
law lib_keeps_words:
  for +lib: String
  for +pwd: String
  for +prog: String
  for +words: List<&2, String>
  {D3.past(6n, HHop.lib.line(lib, pwd, prog, words)) == words : List<&2, String>}

# LAW: a command run in a member reads the root's lock, the workspace's only
# one
law lock_member:
  for +top: String
  for +root: List<&2, String>
  for hd: String
  for tl: List<&2, String>
  {HHop.lock(top, RRoot.Within{root, hd <> tl}) == Path.join(Path.join(top, WWorkspace.segs.text(root)),
      "ez.lock.toml") : String}

# LAW: and one run at the root reads the lock beside it
law lock_own:
  for top: String
  for root: List<&2, String>
  {HHop.lock(top, RRoot.Within{root, []}) == "ez.lock.toml" : String}
