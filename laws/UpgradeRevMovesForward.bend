# An upgraded rev-only dependency moves to the default branch tip only when
# its pin is an ancestor of that tip, and stays a commit pin. Otherwise the
# upgrade refuses with exit 1.
#
# This guarantee and laws/UpgradeTagFollows.bend are proved in the same way.
# Their laws are over `P.ledger.next`, the model `ez lock --upgrade` renders
# into ez.toml: a pin by its commit alone moves only to the default branch
# tip the remote named, when the remote said the tip descends from it, keeps
# no tag, and, when the upgrade asks about it and does not refuse, is at
# that tip; a pin through a tag keeps its tag, moves only to the commit the
# remote names for the tag along its history, and is at that commit when the
# upgrade does not refuse; and a tip off the pin's history, or a pinned
# commit whose checkout no longer agrees with the pin, makes `P.refuses`
# true, which is a plan with no effect (laws/RefusalWritesNothing.bend) that
# the interpreter ends with exit 1 (trusted in src/ez/app.bend). That the
# bytes of ez.toml read back as that model is
# laws/WrittenLedgerReadsBack.bend, and that the remote's refs and ancestry
# are true of the repository is trusted in src/git/git.bend.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/upgrade.bend as U
import ../src/lock/plan.bend as P
import ../src/git/git.bend as Git
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ./defs/LockInputs.bend as D1

# whether a source is pinned by its commit alone, with no tag
def rev_only.src(src: M.Source) -> Bool:
  match src:
    case M.Hub{_named}:
      False{}
    case M.Git{_url, _rev, tag, _root, _nar, _vend}:
      String.is_empty(tag)
    case M.Member{_path, _named}:
      False{}

# whether a dependency is pinned by its commit alone
def rev_only(dep: M.Dep) -> Bool:
  rev_only.src(M.source.dep(dep))

# the pin the upgrade leaves for the dependency named `n`, against the one
# ez.toml records and the default branch tip the remote named for it
def forward.ok(+world: W.World, +name: String) -> Bool:
  D1.moved.ok(Up.forward(D1.ups(world), M.source.url(D1.pin(world, name))), D1.ups(world),
    W.dep(world, name), M.dep(P.ledger.next(world), name))

# LAW: a dependency pinned by its commit alone moves, if it moves at all, to
# the default branch tip the remote named, and only when the remote said that
# tip descends from the pin; and it stays a commit pin, since it keeps the tag
# it had, which is none. Whatever else the upgrade does, and whether or not it
# refuses.
law upgrade_forward_moves_onward:
  for +w: W.World
  for +n: String
  for bare: {rev_only(W.dep(w, n)) == True{} : Bool}
  {forward.ok(w, n) == True{} : Bool}

# LAW: and when `ez lock --upgrade` asks about it, and the tip the remote
# names is another commit that the remote says does not descend from the
# pin, the upgrade refuses, so it writes nothing and exits 1
# (laws/RefusalWritesNothing.bend)
law upgrade_forward_refuses_off:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +bare: {rev_only(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for head: {Up.forward(D1.ups(w), M.source.url(D1.pin(w, n))) == Up.At{tip, tag, branch} : Up.Tip}
  for moved: {String.eq(M.source.rev(D1.pin(w, n)), tip) == False{} : Bool}
  for off: {Up.onward(D1.ups(w), Up.Above{M.source.url(D1.pin(w, n)), M.source.rev(D1.pin(w, n)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {P.refuses(w) == True{} : Bool}

# LAW: and when `ez lock --upgrade` asks about it and does not refuse, it is
# at the default branch tip the remote named: moved there, or there already
law upgrade_forward_reaches_tip:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +bare: {rev_only(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for head: {Up.forward(D1.ups(w), M.source.url(D1.pin(w, n))) == Up.At{tip, tag, branch} : Up.Tip}
  for ok: {P.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(M.dep(P.ledger.next(w), n))) == tip : String}

# The default branch tip `ez lock --upgrade` moves a pin by its commit alone
# to is `tip.rev` of what `ls-remote --symref <url> HEAD` printed: the commit
# on HEAD's own row, and not the symref row above it.

# LAW: the tip is the commit HEAD's commit row names
law tip_of_head:
  for +rev: String
  for rest: List<&2, Git.Row>
  for e: {True{} == Git.is_rev(rev) : Bool}
  {Git.tip.rev(Git.Row{rev, "HEAD"} <> rest) == rev : String}

# LAW: a row that is not HEAD's names no tip
law tip_skips_other:
  for +rev: String
  for +name: String
  for rest: List<&2, Git.Row>
  for e: {False{} == String.eq(name, "HEAD") : Bool}
  {Git.tip.rev(Git.Row{rev, name} <> rest) == Git.tip.rev(rest) : String}

# LAW: nor does HEAD's symref row, whose first field is not a commit
law tip_skips_symref:
  for +rev: String
  for rest: List<&2, Git.Row>
  for e: {False{} == Git.is_rev(rev) : Bool}
  {Git.tip.rev(Git.Row{rev, "HEAD"} <> rest) == Git.tip.rev(rest) : String}
