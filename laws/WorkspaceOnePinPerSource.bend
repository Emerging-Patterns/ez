# Across a workspace a git source, as the root reads it, has one pin: `ez
# lock` refuses, writing nothing, when two declarations of it record a
# different `rev` or `tag`. `ez add` in a workspace, of a source the workspace
# pins, takes with no ref the tag it is pinned at, or its commit when it has
# no tag; with that tag or commit it goes on as given; with any other ref it
# refuses, naming the pin and `ez lock --upgrade --package`, and writes
# nothing. A hub package added by its `<name>@<version>` takes no ref. `ez
# lock --upgrade` at a workspace root is planned on the joint ledger, so it
# moves a source once for every ledger that records it; each such ledger's
# dependency or tool takes the new hash, entry, commit, tag, root and narHash
# and keeps its own source path and vendor bit. It writes the lock the lock
# planner plans on the joint ledger, and refused it writes nothing.
#
# also rests on: laws/UpRefusalWritesNothing.bend, laws/UpWritesTheLock.bend
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/ez/target.bend as Tgt
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/pin.bend as Pin

# LAW: and every git source, as the root reads it, is pinned at one commit
# and one tag across the workspace
law combine_needs_pins:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.pins(J.all.deps(root, ms)) == True{} : Bool}

# ---------------------------------------------------------------------------
# one pin per source (laws/WorkspaceOnePinPerSource.bend)

# LAW: for a project of its own, `ez lock` runs the plan the lock planner
# makes, plain or `--upgrade`, as it always has
law up_alone:
  for +world: W.World
  {UUp.plan(UUp.Alone{}, world) == P.plan(world) : P.Plan}

# LAW: and a plain lock at a workspace root runs it too, since it writes no
# ledger back, unless a committed line names the hash the lock being
# rewritten records for a member that has moved since
# (laws/HashedMemberMovesCascade.bend)
law up_plain:
  for +back: UUp.Back
  for +world: W.World
  for ev: {W.args.upgrade(world) == False{} : Bool}
  for es: {UUp.stale(back, world) == "" : String}
  {UUp.plan(back, world) == P.plan(world) : P.Plan}

# LAW: an upgrade moves a ledger's git dependency to the pin the joint ledger
# gives its name, its hash, entry, commit, tag, root and narHash, and keeps
# the source as that ledger records it, relative to its own directory, and its
# vendor bit
law pin_back:
  for +nn: String
  for hh: String
  for ee: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for +vend: Bool
  for +js: List<&2, M.Dep>
  for jn: String
  for +jh: String
  for +je: String
  for ju: String
  for +jr: String
  for +jt: String
  for +jo: String
  for +jnar: String
  for jv: Bool
  for ev: {M.find(js, nn) == M.Dep{jn, jh, je, M.Git{ju, jr, jt, jo, jnar, jv}} : M.Dep}
  {UUp.dep.back(M.Dep{nn, hh, ee, M.Git{url, rev, tag, root, nar, vend}}, js)
    == M.Dep{nn, jh, je, M.Git{url, jr, jt, jo, jnar, vend}} : M.Dep}

# LAW: and moves a tool's pin the same way, keeping what it builds
law tool_pin_back:
  for +nn: String
  for +ee: String
  for +bb: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for +vend: Bool
  for +ts: List<&2, M.Tool>
  for jn: String
  for je: String
  for jb: String
  for ju: String
  for +jr: String
  for +jt: String
  for +jo: String
  for +jnar: String
  for jv: Bool
  for ev: {M.tool.find(ts, nn) == M.Tool{jn, je, jb, M.Git{ju, jr, jt, jo, jnar, jv}} : M.Tool}
  {UUp.tool.back(M.Tool{nn, ee, bb, M.Git{url, rev, tag, root, nar, vend}}, ts)
    == M.Tool{nn, ee, bb, M.Git{url, jr, jt, jo, jnar, vend}} : M.Tool}

# LAW: `ez add` of a source no member records goes on with the ref it was
# given
law ref_unpinned:
  for nv: String
  for +url: String
  for +ref: String
  {Pin.ref.at(M.Hub{nv}, url, ref) == Pin.Given{ref} : Pin.Ref}

# LAW: with no ref, of a source the workspace pins with a tag, it takes that
# tag
law ref_takes_tag:
  for url: String
  for +ju: String
  for +rev: String
  for +ch: Char
  for +tt: String
  for jo: String
  for jn: String
  for jv: Bool
  {Pin.ref.at(M.Git{ju, rev, SCon{ch, tt}, jo, jn, jv}, url, "") == Pin.Given{SCon{ch, tt}} : Pin.Ref}

# LAW: and of one it pins by its commit alone, that commit
law ref_takes_rev:
  for url: String
  for +ju: String
  for +rev: String
  for jo: String
  for jn: String
  for jv: Bool
  {Pin.ref.at(M.Git{ju, rev, "", jo, jn, jv}, url, "") == Pin.Given{rev} : Pin.Ref}

# LAW: a ref the workspace's pin is recorded by, its tag, goes on as given
law ref_keeps_pin:
  for url: String
  for +ju: String
  for +rev: String
  for +ch: Char
  for +tt: String
  for jo: String
  for jn: String
  for jv: Bool
  {Pin.ref.at(M.Git{ju, rev, SCon{ch, tt}, jo, jn, jv}, url, SCon{ch, tt}) == Pin.Given{SCon{ch, tt}} : Pin.Ref}

# LAW: and any other ref is refused, naming the pin and the upgrade that moves
# it, so a member never adds a second commit of one source
law ref_holds_other:
  for +url: String
  for +ju: String
  for +rev: String
  for +tag: String
  for jo: String
  for jn: String
  for jv: Bool
  for +rc: Char
  for +rt: String
  for et: {String.eq(SCon{rc, rt}, tag) == False{} : Bool}
  for er: {String.eq(SCon{rc, rt}, rev) == False{} : Bool}
  {Pin.ref.at(M.Git{ju, rev, tag, jo, jn, jv}, url, SCon{rc, rt})
    == Pin.Held{"ez: the workspace pins " ++ url ++ " at " ++ Pin.held(rev, tag) ++
      "; move it for every member with ez lock --upgrade --package"} : Pin.Ref}

# LAW: a hub package added by its `<name>@<version>` has no ref to take
law ref_named_free:
  for +pins: List<&2, M.Dep>
  for +dir: String
  for +home: String
  for +target: String
  for +ref: String
  for ev: {Tgt.aim.named(Tgt.aim(target)) == True{} : Bool}
  {Pin.ref(pins, dir, home, target, ref) == Pin.Given{ref} : Pin.Ref}
