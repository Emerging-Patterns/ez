# An upgraded tagged dependency re-resolves its tag. A tag that now names a
# commit the pin does not descend to, or a pinned commit whose tree no longer
# hashes to the pin, stops the upgrade with exit 1.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/upgrade.bend as U
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ./defs/LockInputs.bend as D1

# whether a source is pinned through a tag
def tagged.src(src: M.Source) -> Bool:
  match src:
    case M.Hub{_named}:
      False{}
    case M.Git{_url, _rev, tag, _root, _nar, _vend}:
      Bool.not(String.is_empty(tag))
    case M.Member{_path, _named}:
      False{}

# whether a dependency is pinned through a tag
def tagged(dep: M.Dep) -> Bool:
  tagged.src(M.source.dep(dep))

# and against the commit the remote named for its tag
def follow.ok(+world: W.World, +name: String) -> Bool:
  D1.moved.ok(Up.follow(D1.ups(world), M.source.url(D1.pin(world, name)), M.source.tag(D1.pin(world, name))),
    D1.ups(world), W.dep(world, name), M.dep(P.ledger.next(world), name))

# LAW: a dependency pinned through a tag keeps its tag and moves, if it moves
# at all, to the commit the remote names for that tag, and only when the
# remote said that commit descends from the pin
law upgrade_tag_follows:
  for +w: W.World
  for +n: String
  for named: {tagged(W.dep(w, n)) == True{} : Bool}
  {follow.ok(w, n) == True{} : Bool}

# LAW: and when `ez lock --upgrade` asks about it, and the tag now names
# another commit that the remote says does not descend from the pin, the
# upgrade refuses
law upgrade_tag_refuses_off:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +named: {tagged(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for refs: {Up.follow(D1.ups(w), M.source.url(D1.pin(w, n)), M.source.tag(D1.pin(w, n)))
    == Up.At{tip, tag, branch} : Up.Tip}
  for moved: {String.eq(M.source.rev(D1.pin(w, n)), tip) == False{} : Bool}
  for off: {Up.onward(D1.ups(w), Up.Above{M.source.url(D1.pin(w, n)), M.source.rev(D1.pin(w, n)), tip})
    == Up.Asc{False{}} : Up.Asc}
  {P.refuses(w) == True{} : Bool}

# LAW: and when the tag still names the pinned commit, but that commit's
# checkout no longer agrees with the pin, in its hash, its NAR hash or its
# root, the upgrade refuses: the pin drifted
law upgrade_tag_refuses_drift:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for +nar: String
  for +root: String
  for +manifest: String
  for +srcs: List<&2, String>
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +named: {tagged(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for refs: {Up.follow(D1.ups(w), M.source.url(D1.pin(w, n)), M.source.tag(D1.pin(w, n)))
    == Up.At{tip, tag, branch} : Up.Tip}
  for same: {String.eq(M.source.rev(D1.pin(w, n)), tip) == True{} : Bool}
  for co: {Up.checkout(D1.ups(w), Up.Tree{M.source.url(D1.pin(w, n)), M.source.rev(D1.pin(w, n)),
    M.dep.entry(W.dep(w, n))}) == Up.Co{nar, root, manifest, srcs} : Up.Co}
  for drift: {U.agree(M.dep.hash(W.dep(w, n)), Up.hash.kept(M.dep.hash(W.dep(w, n)), manifest),
    M.source.nar(D1.pin(w, n)),
    nar, M.source.root(D1.pin(w, n)), root) == False{} : Bool}
  {P.refuses(w) == True{} : Bool}

# LAW: and a pin through a tag that `ez lock --upgrade` asks about, when it
# does not refuse, is at the commit the remote names for its tag: the tag is
# re-resolved, not only allowed to be
law upgrade_tag_resolves:
  for +w: W.World
  for +n: String
  for +tip: String
  for +tag: String
  for +branch: String
  for up: {W.args.upgrade(w) == True{} : Bool}
  for +named: {tagged(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for refs: {Up.follow(D1.ups(w), M.source.url(D1.pin(w, n)), M.source.tag(D1.pin(w, n)))
    == Up.At{tip, tag, branch} : Up.Tip}
  for ok: {P.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(M.dep(P.ledger.next(w), n))) == tip : String}
