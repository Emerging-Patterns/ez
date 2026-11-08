# In a workspace, `ez lock` writes one `ez.lock.toml`, at the root, planned
# from the joint ledger: the root's `[package]` table with every dependency
# and tool of the root and of every member, a member's relative path source
# read from the member's directory, each name at its first declaration. Two
# declarations of one name that differ, a member naming another hub than the
# root's, and a member ledger that does not parse are refused, and nothing
# is written. A ledger with no `[workspace]` table is locked as before.
# laws/LockReproducible.bend, laws/LockIdempotent.bend and
# laws/PlainLockKeepsLedger.bend hold of a workspace: the lock is a function
# of the members' ledgers and the committed tree, a rerun writes the same
# bytes, and a plain lock writes no path but the root's lock, so no member's
# ledger or lock.
#
# also rests on: laws/LockIdempotent.bend, laws/LockReproducible.bend,
# laws/PlainLockKeepsLedger.bend, laws/PlainLockWritesOnlyLock.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J

# LAW: and so it writes no member's ledger: no path that ends in a directory's
# `ez.toml`
law plain_lock_keeps_members:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  for +pre: String
  {P.put(w, pre ++ "/ez.toml") == P.Kept{} : P.Wrote}

# ---------------------------------------------------------------------------
# one lock (laws/WorkspaceLocksOnce.bend)

# LAW: a ledger with no `[workspace]` table is no workspace root, and is
# locked as it always was
law joint_lone:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for ev: {WWorkspace.spec.of(text) == WWorkspace.Lone{} : WWorkspace.Read}
  {J.joint(text, fs, files) == J.Lone{} : J.Joint}

# LAW: and the lock planner reads that ledger's own text
law lone_locks_own:
  for own: Maybe<&2, String>
  {J.joint.text(J.Lone{}, own) == own : Maybe<&2, String>}

# LAW: a `[workspace]` table that cannot be read leaves nothing to lock from
law joint_bad_table:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for +why: String
  for ev: {WWorkspace.spec.of(text) == WWorkspace.Bad{why} : WWorkspace.Read}
  {J.joint(text, fs, files) == J.Clash{why} : J.Joint}

# LAW: and so does a workspace with no member set
# (laws/WorkspaceMembersChosen.bend)
law joint_refused_members:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for +spec: WWorkspace.Spec
  for +why: String
  for ev: {WWorkspace.spec.of(text) == WWorkspace.Root{spec} : WWorkspace.Read}
  for em: {WWorkspace.members(spec, WWorkspace.root.of(text),
      J.ledgers(fs)) == WWorkspace.Refused{why} : WWorkspace.Members}
  {J.joint(text, fs, files) == J.Clash{why} : J.Joint}

# LAW: members that can be joined are: the root's package, with every
# dependency and tool of the root and the members at its first declaration
law combine_when_ok:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for ev: {J.ok(root, ms) == True{} : Bool}
  {J.combine(root, ms) == J.Joint{J.joined(root, ms)} : J.Joint}

# LAW: and members that cannot be are refused, with the reason why
law combine_refused:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for ev: {J.ok(root, ms) == False{} : Bool}
  {J.combine(root, ms) == J.Clash{J.why(root, ms)} : J.Joint}

# LAW: the joint ledger's dependency of a name is the first declaration of it,
# among the root's and then every member's, and a name no one declares is
# none in it either
law firsts_find:
  for ds: List<&2, M.Dep>
  for +name: String
  {M.find(J.firsts(ds), name) == M.find(ds, name) : M.Dep}

# LAW: and so is its tool of a name
law tools_firsts_find:
  for ts: List<&2, M.Cli>
  for +name: String
  {M.tool.find(J.tools.firsts(ts), name) == M.tool.find(ts, name) : M.Cli}

# LAW: joined members name the root's hub
law combine_needs_hub:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.hubs(J.root.hub(root), ms) == True{} : Bool}

# LAW: and every declaration of a dependency agrees with the first, so no
# member's is dropped for another's
law combine_needs_deps:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.agree(J.all.deps(root, ms)) == True{} : Bool}

# LAW: and every declaration of a tool
law combine_needs_tools:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.tools.agree(J.all.tools(root, ms)) == True{} : Bool}
