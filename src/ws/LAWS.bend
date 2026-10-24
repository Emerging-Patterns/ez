# ws: the laws. The human states them; PROOF.bend must prove them. A
# workspace's member set is decided from the root ledger's `[workspace]`
# table and the ledgers git lists under the root, so what is stated here is
# that decision: an entry names a directory or every directory directly under
# one, a path that climbs or names itself by `.` is never one, and the
# members are exactly the listed directories no exclusion takes back, once
# nothing is refused. A command run in a directory finds its root by reading
# the ledger of each directory from there up to the top of the checkout,
# nearest first, and the first workspace root that claims the directory is
# its root.
import Base
import ./workspace.bend as W
import 0xc5d9d3e28b79ea98be22eb42c7e37802/main.bend as E
import ./root.bend as R
import ./joint.bend as J
import ./hop.bend as H
import ./up.bend as U
import ./moved.bend as Mv
import ./doctor.bend as Doc
import ../doctor/plan.bend as DP
import ../doctor/world.bend as DW
import ../ledger/upgrade.bend as LU
import ./pin.bend as Pin
import ../ez/target.bend as Tgt
import ../lock/world.bend as LW
import ../lock/plan.bend as LP
import ../pkg/path.bend as P
import ../pkg/pkg.bend as K
import ../lock/lock.bend as L
import ../ledger/ignore.bend as I
import ../toml/toml.bend as T
import ../pub/plan.bend as PP
import ../ledger/manifest.bend as M

# a path every path that starts with it extends. Law vocabulary: ez never
# calls it.
def prefix(ps: List<&2, String>, ds: List<&2, String>) -> Bool:
  match ps:
    case []:
      True{}
    case +ph <> pt:
      match ds:
        case []:
          False{}
        case +dh <> dt:
          Bool.and(String.eq(ph, dh), prefix(pt, dt))

# LAW: a path cut at its last segment, when that segment is the word, is the
# path before it. `libs/*` cut at `*` is `libs`, and `cli/ez.toml` cut at
# `ez.toml` is `cli`.
# EZ-WS-1
law cut_last:
  for +ds: List<&2, String>
  for +word: String
  {W.cut(List.append(&2, String, ds, [word]), word) == Some{ds}
    : Maybe<&2, List<&2, String>>}

# LAW: an entry written `<dir>/*` names the directories under `<dir>`
# EZ-WS-1
law entry_under:
  for +ds: List<&2, String>
  {W.entry.of(List.append(&2, String, ds, ["*"])) == W.Under{ds} : W.Entry}

# LAW: and any other entry names the directory it is written as
# EZ-WS-1
law entry_plain:
  for +ss: List<&2, String>
  for ev: {W.cut(ss, "*") == None{} : Maybe<&2, List<&2, String>>}
  {W.entry.of(ss) == W.Plain{ss} : W.Entry}

# LAW: a directory one segment below another is under it
# EZ-WS-1
law under_child:
  for +ps: List<&2, String>
  for +nn: String
  {W.under(ps, List.append(&2, String, ps, [nn])) == True{} : Bool}

# LAW: and one two or more segments below it is not
# EZ-WS-1
law under_deeper:
  for +ps: List<&2, String>
  for nn: String
  for mm: String
  for rest: List<&2, String>
  {W.under(ps, List.append(&2, String, ps, nn <> mm <> rest)) == False{} : Bool}

# LAW: a directory under another starts with the other's segments, so
# `<dir>/*` names nothing outside `<dir>`
# EZ-WS-1
law under_prefix:
  for ps: List<&2, String>
  for ds: List<&2, String>
  for +ev: {W.under(ps, ds) == True{} : Bool}
  {prefix(ps, ds) == True{} : Bool}

# LAW: a path with a segment no member's path may have is not one, wherever
# that segment stands
# EZ-WS-1
law segs_bad:
  for +ps: List<&2, String>
  for +bad: String
  for qs: List<&2, String>
  for ev: {W.seg.ok(bad) == False{} : Bool}
  {W.segs.ok(List.append(&2, String, ps, bad <> qs)) == False{} : Bool}

# LAW: an empty segment, which a leading `/` or a `//` makes, is refused
# EZ-WS-1
law seg_empty_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {W.segs.ok(List.append(&2, String, ps, "" <> qs)) == False{} : Bool}

# LAW: and so is `.`
# EZ-WS-1
law seg_dot_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {W.segs.ok(List.append(&2, String, ps, "." <> qs)) == False{} : Bool}

# LAW: and `..`, so no member climbs out of the root
# EZ-WS-1
law seg_up_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {W.segs.ok(List.append(&2, String, ps, ".." <> qs)) == False{} : Bool}

# LAW: and a `*` anywhere but the end of an entry, which is no glob ez reads
# EZ-WS-1
law seg_star_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {W.segs.ok(List.append(&2, String, ps, "*" <> qs)) == False{} : Bool}

# LAW: an entry that names a directory names it wherever it stands among the
# entries
# EZ-WS-1
law listed_anywhere:
  for +fs: List<&2, W.Entry>
  for ee: W.Entry
  for es: List<&2, W.Entry>
  for +ds: List<&2, String>
  for ev: {W.hit(ee, ds) == True{} : Bool}
  {W.listed(List.append(&2, W.Entry, fs, ee <> es), ds) == True{} : Bool}

# LAW: an excluded directory is not a member, whatever names it
# EZ-WS-1
law excluded_not_chosen:
  for es: List<&2, W.Entry>
  for +ex: List<&2, List<&2, String>>
  for +ds: List<&2, String>
  for ev: {W.has(ex, ds) == True{} : Bool}
  {W.chosen(W.Spec{es, ex}, ds) == False{} : Bool}

# LAW: the members are exactly the ledgers' directories that an entry names
# and no exclusion does: every one of them, and nothing else
# EZ-WS-1
law picks_exactly:
  for +spec: W.Spec
  for +ls: List<&2, W.Ledger>
  for +ds: List<&2, String>
  {W.has(W.dirs.of(W.picks(spec, ls)), ds)
    == Bool.and(W.has(W.dirs.of(ls), ds), W.chosen(spec, ds)) : Bool}

# LAW: an entry naming a directory as it is, with no committed ez.toml there,
# leaves the workspace with no member set, wherever it stands
# EZ-WS-1
law present_anywhere:
  for +fs: List<&2, W.Entry>
  for +ps: List<&2, String>
  for es: List<&2, W.Entry>
  for +found: List<&2, List<&2, String>>
  for ev: {W.has(found, ps) == False{} : Bool}
  {W.present(List.append(&2, W.Entry, fs, W.Plain{ps} <> es), found) == False{} : Bool}

# LAW: a workspace with a member set has the root as a member exactly when its
# ledger has a package, and the picked directories as the rest
# EZ-WS-1
law members_when_ok:
  for +spec: W.Spec
  for +root: W.Root
  for +ls: List<&2, W.Ledger>
  for ev: {W.ok(spec, root, ls) == True{} : Bool}
  {W.members(spec, root, ls) == W.Members{W.root.member(root), W.dirs.of(W.picks(spec, ls))}
    : W.Members}

# LAW: and one with none is refused, with the reason why
# EZ-WS-1
law members_refused:
  for +spec: W.Spec
  for +root: W.Root
  for +ls: List<&2, W.Ledger>
  for ev: {W.ok(spec, root, ls) == False{} : Bool}
  {W.members(spec, root, ls) == W.Refused{W.why(spec, root, ls)} : W.Members}

# LAW: a member set is had only when every entry names a directory a
# workspace can name
# EZ-WS-1
law ok_needs_entries:
  for +es: List<&2, W.Entry>
  for +ex: List<&2, List<&2, String>>
  for +root: W.Root
  for +ls: List<&2, W.Ledger>
  for +ev: {W.ok(W.Spec{es, ex}, root, ls) == True{} : Bool}
  {W.entries.ok(es) == True{} : Bool}

# LAW: and every entry naming a directory as it is names one with a committed
# ez.toml
# EZ-WS-1
law ok_needs_present:
  for +es: List<&2, W.Entry>
  for +ex: List<&2, List<&2, String>>
  for +root: W.Root
  for +ls: List<&2, W.Ledger>
  for +ev: {W.ok(W.Spec{es, ex}, root, ls) == True{} : Bool}
  {W.present(es, W.dirs.of(ls)) == True{} : Bool}

# LAW: and no member is a workspace root of its own
# EZ-WS-1
law ok_needs_unnested:
  for +spec: W.Spec
  for +root: W.Root
  for +ls: List<&2, W.Ledger>
  for +ev: {W.ok(spec, root, ls) == True{} : Bool}
  {W.unnested(W.picks(spec, ls)) == True{} : Bool}

# LAW: and no two members, the root among them, share a package name
# EZ-WS-1
law ok_needs_names:
  for +spec: W.Spec
  for +root: W.Root
  for +ls: List<&2, W.Ledger>
  for +ev: {W.ok(spec, root, ls) == True{} : Bool}
  {W.distinct(W.names(root, W.picks(spec, ls))) == True{} : Bool}

# ---------------------------------------------------------------------------
# finding the root (EZ-WS-2)

# every directory asked about after the first, nearest first. Law
# vocabulary: ez never calls it.
def asks.rest(here: List<&2, String>) -> List<&2, R.Ask>:
  match here:
    case []:
      []
    case +hd <> +tl:
      List.append(&2, R.Ask, R.asks.under(hd, asks.rest(tl)), [R.Ask{[], hd <> tl}])

# every directory asked about before the top of the checkout
def asks.init(here: List<&2, String>) -> List<&2, R.Ask>:
  match here:
    case []:
      []
    case +hd <> +tl:
      R.asks.under(hd, R.asks(tl))

# whether every directory asked about, followed down by its path to where ez
# runs, is where ez runs
def splits(xs: List<&2, R.Ask>, +here: List<&2, String>) -> Bool:
  match xs:
    case []:
      True{}
    case R.Ask{ds, rs} <> tl:
      Bool.and(W.segs.eq(List.append(&2, String, ds, rs), here), splits(tl, here))

# whether a directory's ledger says nothing of a workspace: it has none, or it
# has no `[workspace]` table
def quiet.read(rd: W.Read) -> Bool:
  match rd:
    case W.Lone{}:
      True{}
    case W.Bad{_why}:
      False{}
    case W.Root{_spec}:
      False{}

# whether a directory read says nothing of a workspace
def quiet.one(text: Maybe<&2, String>) -> Bool:
  match text:
    case None{}:
      True{}
    case Some{tt}:
      quiet.read(W.spec.of(tt))

# whether no directory read says anything of a workspace
def quiet(ups: List<&2, R.Up>) -> Bool:
  match ups:
    case []:
      True{}
    case R.Up{_ds, _rs, tx} <> tl:
      Bool.and(quiet.one(tx), quiet(tl))

# LAW: the first directory asked about is where ez runs, as its own root
# would be
# EZ-WS-2
law asks_nearest:
  for +here: List<&2, String>
  {R.asks(here) == R.Ask{here, []} <> asks.rest(here) : List<&2, R.Ask>}

# LAW: and the last is the top of the checkout, from which ez runs the whole
# path down
# EZ-WS-2
law asks_top:
  for +here: List<&2, String>
  {R.asks(here) == List.append(&2, R.Ask, asks.init(here), [R.Ask{[], here}]) : List<&2, R.Ask>}

# LAW: every directory asked about is above where ez runs, by the path it is
# asked with
# EZ-WS-2
law asks_split:
  for +here: List<&2, String>
  {splits(R.asks(here), here) == True{} : Bool}

# LAW: a directory with no ez.toml is passed by
# EZ-WS-2
law root_skips_none:
  for ds: List<&2, String>
  for rs: List<&2, String>
  for ups: List<&2, R.Up>
  {R.root.go(R.Up{ds, rs, None{}} <> ups) == R.root.go(ups) : R.Found}

# LAW: and so is one whose ledger has no `[workspace]` table
# EZ-WS-2
law root_skips_lone:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, R.Up>
  for ev: {W.spec.of(tt) == W.Lone{} : W.Read}
  {R.root.go(R.Up{ds, rs, Some{tt}} <> ups) == R.root.go(ups) : R.Found}

# LAW: a `[workspace]` table that could not be read stops the search, so a
# command never takes a directory for a project of its own because the table
# above it was broken
# EZ-WS-2
law root_bad_refuses:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, R.Up>
  for +why: String
  for ev: {W.spec.of(tt) == W.Bad{why} : W.Read}
  {R.root.go(R.Up{ds, rs, Some{tt}} <> ups) == R.Broken{why} : R.Found}

# LAW: a workspace root that claims where ez runs is its root, whatever is
# above it
# EZ-WS-2
law root_claims_it:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, R.Up>
  for +spec: W.Spec
  for ev: {W.spec.of(tt) == W.Root{spec} : W.Read}
  for ec: {R.claims(spec, rs) == True{} : Bool}
  {R.root.go(R.Up{ds, rs, Some{tt}} <> ups) == R.Within{ds, rs} : R.Found}

# LAW: and one that does not is passed by
# EZ-WS-2
law root_passes_by:
  for +ds: List<&2, String>
  for +rs: List<&2, String>
  for +tt: String
  for +ups: List<&2, R.Up>
  for +spec: W.Spec
  for ev: {W.spec.of(tt) == W.Root{spec} : W.Read}
  for ec: {R.claims(spec, rs) == False{} : Bool}
  {R.root.go(R.Up{ds, rs, Some{tt}} <> ups) == R.root.go(ups) : R.Found}

# LAW: with no workspace above it, a directory is a project of its own
# EZ-WS-2
law root_none:
  for ups: List<&2, R.Up>
  for +ev: {quiet(ups) == True{} : Bool}
  {R.root.go(ups) == R.Alone{} : R.Found}

# LAW: a workspace root claims itself, whatever its members are
# EZ-WS-2
law claims_self:
  for +spec: W.Spec
  {R.claims(spec, []) == True{} : Bool}

# LAW: and claims a directory below it exactly when that directory is a
# member (EZ-WS-1)
# EZ-WS-2
law claims_member:
  for +spec: W.Spec
  for +hd: String
  for +tl: List<&2, String>
  {R.claims(spec, hd <> tl) == W.chosen(spec, hd <> tl) : Bool}

# ---------------------------------------------------------------------------
# one lock (EZ-WS-3)

# LAW: a ledger with no `[workspace]` table is no workspace root, and is
# locked as it always was
# EZ-WS-3
law joint_lone:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for ev: {W.spec.of(text) == W.Lone{} : W.Read}
  {J.joint(text, fs, files) == J.Lone{} : J.Joint}

# LAW: and the lock planner reads that ledger's own text
# EZ-WS-3
law lone_locks_own:
  for own: Maybe<&2, String>
  {J.joint.text(J.Lone{}, own) == own : Maybe<&2, String>}

# LAW: a `[workspace]` table that cannot be read leaves nothing to lock from
# EZ-WS-3
law joint_bad_table:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for +why: String
  for ev: {W.spec.of(text) == W.Bad{why} : W.Read}
  {J.joint(text, fs, files) == J.Clash{why} : J.Joint}

# LAW: and so does a workspace with no member set (EZ-WS-1)
# EZ-WS-3
law joint_refused_members:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for +spec: W.Spec
  for +why: String
  for ev: {W.spec.of(text) == W.Root{spec} : W.Read}
  for em: {W.members(spec, W.root.of(text), J.ledgers(fs)) == W.Refused{why} : W.Members}
  {J.joint(text, fs, files) == J.Clash{why} : J.Joint}

# LAW: members that can be joined are: the root's package, with every
# dependency and tool of the root and the members at its first declaration
# EZ-WS-3
law combine_when_ok:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for ev: {J.ok(root, ms) == True{} : Bool}
  {J.combine(root, ms) == J.Joint{J.joined(root, ms)} : J.Joint}

# LAW: and members that cannot be are refused, with the reason why
# EZ-WS-3
law combine_refused:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for ev: {J.ok(root, ms) == False{} : Bool}
  {J.combine(root, ms) == J.Clash{J.why(root, ms)} : J.Joint}

# LAW: the joint ledger's dependency of a name is the first declaration of it,
# among the root's and then every member's, and a name no one declares is
# none in it either
# EZ-WS-3
law firsts_find:
  for ds: List<&2, M.Dep>
  for +name: String
  {M.find(J.firsts(ds), name) == M.find(ds, name) : M.Dep}

# LAW: and so is its tool of a name
# EZ-WS-3
law tools_firsts_find:
  for ts: List<&2, M.Tool>
  for +name: String
  {M.tool.find(J.tools.firsts(ts), name) == M.tool.find(ts, name) : M.Tool}

# LAW: joined members name the root's hub
# EZ-WS-3
law combine_needs_hub:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.hubs(J.root.hub(root), ms) == True{} : Bool}

# LAW: and every declaration of a dependency agrees with the first, so no
# member's is dropped for another's
# EZ-WS-3
law combine_needs_deps:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.agree(J.all.deps(root, ms)) == True{} : Bool}

# LAW: and every git source, as the root reads it, is pinned at one commit
# and one tag across the workspace
# EZ-WS-4
law combine_needs_pins:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.pins(J.all.deps(root, ms)) == True{} : Bool}

# LAW: and every declaration of a tool
# EZ-WS-3
law combine_needs_tools:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +ev: {J.ok(root, ms) == True{} : Bool}
  {J.tools.agree(J.all.tools(root, ms)) == True{} : Bool}

# ---------------------------------------------------------------------------
# where a whole-workspace command runs (EZ-WS-2)

# a list with its first `count` words dropped, the count looked at first.
# Law vocabulary: ez never calls it.
def past(count: Nat, xs: List<&2, String>) -> List<&2, String>:
  match count:
    case 0n:
      xs
    case 1n+kk:
      match xs:
        case []:
          []
        case _hd <> tl:
          past(kk, tl)

# LAW: a command run in a project of its own runs where it is
# EZ-WS-2
law hop_alone:
  for top: String
  {H.hop(top, R.Alone{}) == H.Here{} : H.Hop}

# LAW: and so does one run at its workspace's root
# EZ-WS-2
law hop_at_root:
  for top: String
  for root: List<&2, String>
  {H.hop(top, R.Within{root, []}) == H.Here{} : H.Hop}

# LAW: one run in a member runs again at the root's directory
# EZ-WS-2
law hop_member:
  for +top: String
  for +root: List<&2, String>
  for hd: String
  for tl: List<&2, String>
  {H.hop(top, R.Within{root, hd <> tl}) == H.Hop{P.join(top, W.segs.text(root))} : H.Hop}

# LAW: and one whose search was refused runs nowhere, saying why
# EZ-WS-2
law hop_broken:
  for top: String
  for +why: String
  {H.hop(top, R.Broken{why}) == H.Stop{why} : H.Hop}

# LAW: the run at the root is handed every word the command was run with,
# unchanged and in order
# EZ-WS-2
law hop_keeps_words:
  for +dir: String
  for +pwd: String
  for +prog: String
  for +words: List<&2, String>
  {past(6n, H.line(dir, pwd, prog, words)) == words : List<&2, String>}

# ---------------------------------------------------------------------------
# one pin per source (EZ-WS-4)

# LAW: for a project of its own, `ez lock` runs the plan the lock planner
# makes, plain or `--upgrade`, as it always has
# EZ-WS-4
law up_alone:
  for +world: LW.World
  {U.plan(U.Alone{}, world) == LP.plan(world) : LP.Plan}

# LAW: and a plain lock at a workspace root runs it too, since it writes no
# ledger back, unless a committed line names the hash the lock being
# rewritten records for a member that has moved since (EZ-WS-7)
# EZ-WS-4
law up_plain:
  for +back: U.Back
  for +world: LW.World
  for ev: {LW.args.upgrade(world) == False{} : Bool}
  for es: {U.stale(back, world) == "" : String}
  {U.plan(back, world) == LP.plan(world) : LP.Plan}

# LAW: an upgrade moves a ledger's git dependency to the pin the joint ledger
# gives its name, its hash, entry, commit, tag, root and narHash, and keeps
# the source as that ledger records it, relative to its own directory, and its
# vendor bit
# EZ-WS-4
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
  {U.dep.back(M.Dep{nn, hh, ee, M.Git{url, rev, tag, root, nar, vend}}, js)
    == M.Dep{nn, jh, je, M.Git{url, jr, jt, jo, jnar, vend}} : M.Dep}

# LAW: and moves a tool's pin the same way, keeping what it builds
# EZ-WS-4
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
  {U.tool.back(M.Tool{nn, ee, bb, M.Git{url, rev, tag, root, nar, vend}}, ts)
    == M.Tool{nn, ee, bb, M.Git{url, jr, jt, jo, jnar, vend}} : M.Tool}

# LAW: an upgrade at a workspace root that refuses writes nothing: no ledger,
# no lock, no tree, and no source it would have rewritten (EZ-OUT-2). The
# World it refuses on is the one it plans on, with every moved member's import
# lines rewritten (EZ-WS-7).
# EZ-WS-4
# EZ-WS-7
law up_refusal_writes_nothing:
  for +back: U.Back
  for +world: LW.World
  for +er: {LP.refuses(U.plans.on(back, world)) == True{} : Bool}
  {LP.writes(U.plan(back, world)) == False{} : Bool}

# LAW: and the lock it writes is the one the lock planner plans on the joint
# ledger: writing the ledgers back in place of the joint one, and the sources
# the member moves rewrite ahead of the plan, leaves the lock as it was
# EZ-WS-4
# EZ-WS-7
law up_writes_the_lock:
  for +back: U.Back
  for +world: LW.World
  for es: {U.stale(back, world) == "" : String}
  {LP.put.plan(U.plan(back, world), LP.lockfile()) == LP.put(U.plans.on(back, world), LP.lockfile()) : LP.Wrote}

# LAW: `ez add` of a source no member records goes on with the ref it was
# given
# EZ-WS-4
law ref_unpinned:
  for nv: String
  for +url: String
  for +ref: String
  {Pin.ref.at(M.Hub{nv}, url, ref) == Pin.Given{ref} : Pin.Ref}

# LAW: with no ref, of a source the workspace pins with a tag, it takes that
# tag
# EZ-WS-4
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
# EZ-WS-4
law ref_takes_rev:
  for url: String
  for +ju: String
  for +rev: String
  for jo: String
  for jn: String
  for jv: Bool
  {Pin.ref.at(M.Git{ju, rev, "", jo, jn, jv}, url, "") == Pin.Given{rev} : Pin.Ref}

# LAW: a ref the workspace's pin is recorded by, its tag, goes on as given
# EZ-WS-4
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
# EZ-WS-4
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
# EZ-WS-4
law ref_named_free:
  for +pins: List<&2, M.Dep>
  for +dir: String
  for +home: String
  for +target: String
  for +ref: String
  for ev: {Tgt.aim.named(Tgt.aim(target)) == True{} : Bool}
  {Pin.ref(pins, dir, home, target, ref) == Pin.Given{ref} : Pin.Ref}

# ---------------------------------------------------------------------------
# a member's own commands use the root's library (EZ-WS-2)

# LAW: a library the environment sets is kept, wherever ez runs
# EZ-WS-2
law lib_keeps_env:
  for top: String
  for found: R.Found
  for +ch: Char
  for +tt: String
  {H.lib(top, found, SCon{ch, tt}) == H.Keep{} : H.Lib}

# LAW: with none set, a command run in a member uses the root's `.ez/lib`
# EZ-WS-2
law lib_member:
  for +top: String
  for +root: List<&2, String>
  for hd: String
  for tl: List<&2, String>
  {H.lib(top, R.Within{root, hd <> tl}, "")
    == H.Set{P.join(P.join(top, W.segs.text(root)), ".ez/lib")} : H.Lib}

# LAW: and one run at the root, or in a project of its own, uses its own, as
# it always did
# EZ-WS-2
law lib_own:
  for top: String
  for root: List<&2, String>
  {H.lib(top, R.Within{root, []}, "") == H.Keep{} : H.Lib}

# LAW: in a project of its own too
# EZ-WS-2
law lib_alone:
  for top: String
  {H.lib(top, R.Alone{}, "") == H.Keep{} : H.Lib}

# LAW: the run with the root's library is handed every word, unchanged and in
# order
# EZ-WS-2
law lib_keeps_words:
  for +lib: String
  for +pwd: String
  for +prog: String
  for +words: List<&2, String>
  {past(6n, H.lib.line(lib, pwd, prog, words)) == words : List<&2, String>}

# LAW: a command run in a member reads the root's lock, the workspace's only
# one
# EZ-WS-2
law lock_member:
  for +top: String
  for +root: List<&2, String>
  for hd: String
  for tl: List<&2, String>
  {H.lock(top, R.Within{root, hd <> tl}) == P.join(P.join(top, W.segs.text(root)), "ez.lock.toml") : String}

# LAW: and one run at the root reads the lock beside it
# EZ-WS-2
law lock_own:
  for top: String
  for root: List<&2, String>
  {H.lock(top, R.Within{root, []}) == "ez.lock.toml" : String}

# ---------------------------------------------------------------------------
# reading the `[workspace]` table (EZ-WS-1)

# LAW: the `[workspace]` table is found among a ledger's tables, wherever it
# stands after the ones before it
# EZ-WS-1
law spec_finds_table:
  for path: String
  for +sub: List<&2, E.Val>
  for rest: List<&2, E.Val>
  {W.spec.rows(E.VPair{"workspace", E.VHead{path, sub}} <> rest) == W.table(sub) : W.Read}

# LAW: and a ledger whose tables hold none is no workspace root
# EZ-WS-1
law spec_none_lone:
  for path: String
  for sub: List<&2, E.Val>
  for +ch: Char
  for +tt: String
  for rest: List<&2, E.Val>
  for ev: {String.eq(SCon{ch, tt}, "workspace") == False{} : Bool}
  {W.spec.rows(E.VPair{SCon{ch, tt}, E.VHead{path, sub}} <> rest) == W.spec.rows(rest) : W.Read}

# LAW: a table's entries and exclusions are the arrays its `members` and
# `exclude` keys hold, each text read as a path's segments
# EZ-WS-1
law table_reads:
  for +rows: List<&2, E.Val>
  for +ms: List<&2, String>
  for +xs: List<&2, String>
  for em: {W.array(rows, "members") == Some{ms} : Maybe<&2, List<&2, String>>}
  for ex: {W.array(rows, "exclude") == Some{xs} : Maybe<&2, List<&2, String>>}
  {W.table(rows) == W.Root{W.Spec{W.entries.of(ms), W.paths.of(xs)}} : W.Read}

# LAW: a `members` that is not an array of strings is refused, never read as
# a shorter list
# EZ-WS-1
law table_refuses_members:
  for +rows: List<&2, E.Val>
  for em: {W.array(rows, "members") == None{} : Maybe<&2, List<&2, String>>}
  {W.table(rows) == W.Bad{"ez: [workspace] members is not a list of strings"} : W.Read}

# LAW: a key's array is the strings it holds
# EZ-WS-1
law array_at_key:
  for +key: String
  for +items: List<&2, E.Val>
  for rest: List<&2, E.Val>
  {W.array(E.VPair{key, E.VArr{items}} <> rest, key) == W.strs(items) : Maybe<&2, List<&2, String>>}

# LAW: and an array holding anything but strings holds none
# EZ-WS-1
law strs_refuses_other:
  for bit: Bool
  for rest: List<&2, E.Val>
  {W.strs(E.VBool{bit} <> rest) == None{} : Maybe<&2, List<&2, String>>}

# ---------------------------------------------------------------------------
# a member as a dependency (EZ-WS-5)

# LAW: a member's section names the member whose `[package] name` is its
# key, and the joint ledger holds that member's package: its hash is the `0x`
# name of the walk from the member's entry over the committed files, with the
# entry it walked from, as a path from the root, and the directory the walk
# writes its paths from; one whose ledger names it neither way is imported by
# its hash
# EZ-WS-5
law member_dep_walked:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +hash: String
  for +root: String
  for fs: List<&2, K.Source>
  for sums: List<&2, K.Item>
  for ef: {J.named(ms, name) == Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}}
    : Maybe<&2, J.Member>}
  for eo: {W.segs.eq(dir, self) == False{} : Bool}
  for en: {PP.naming(pa, pv) == PP.ByHash{} : PP.Named}
  for ew: {K.of(J.entry.at(dir, ee), files) == K.Walked{hash, root, fs, sums} : K.Walked}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}

# LAW: a member whose ledger gives `publish-as` and `version` is imported by
# the name `ez publish` would publish it under, `<publish-as>@<version>.0`,
# and the joint ledger records that name beside its hash
# EZ-WS-5
# EZ-WS-6
law member_dep_named:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +hash: String
  for +root: String
  for fs: List<&2, K.Source>
  for sums: List<&2, K.Item>
  for ef: {J.named(ms, name) == Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}}
    : Maybe<&2, J.Member>}
  for eo: {W.segs.eq(dir, self) == False{} : Bool}
  for +nv: String
  for en: {PP.naming(pa, pv) == PP.ByName{nv} : PP.Named}
  for ew: {K.of(J.entry.at(dir, ee), files) == K.Walked{hash, root, fs, sums} : K.Walked}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}

# LAW: and a section naming a member whose name publish would refuse is
# refused with publish's reason
# EZ-WS-6
law member_dep_unnamed:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for ef: {J.named(ms, name) == Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}}
    : Maybe<&2, J.Member>}
  for eo: {W.segs.eq(dir, self) == False{} : Bool}
  for +why: String
  for en: {PP.naming(pa, pv) == PP.Unnamed{why} : PP.Named}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}

# LAW: the member a section names is the first whose `[package] name` is the
# section's key
# EZ-WS-5
law named_finds:
  for +dir: List<&2, String>
  for +name: String
  for +ee: String
  for +bb: String
  for +hh: String
  for +pa: String
  for +pv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +ms: List<&2, J.Member>
  {J.named(J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}} <> ms, name)
    == Some{J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}}} : Maybe<&2, J.Member>}

# LAW: and a member named otherwise is passed over
# EZ-WS-5
law named_skips:
  for +hd: J.Member
  for +ms: List<&2, J.Member>
  for +name: String
  for en: {String.eq(J.member.name(hd), name) == False{} : Bool}
  {J.named(hd <> ms, name) == J.named(ms, name) : Maybe<&2, J.Member>}

# LAW: a section naming no member is refused
# EZ-WS-5
law member_dep_unknown:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for ef: {J.named(ms, name) == None{} : Maybe<&2, J.Member>}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and no member's " ++
      "[package] is named " ++ name} : J.Res}

# LAW: and so is one naming the member it is written in
# EZ-WS-5
law member_dep_own:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for mm: M.Manifest
  for ef: {J.named(ms, name) == Some{J.Member{dir, mm}} : Maybe<&2, J.Member>}
  for eo: {W.segs.eq(dir, self) == True{} : Bool}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
    : J.Res}

# LAW: a member's section records no hash: one that gives a hash is refused
# EZ-WS-5
law member_dep_hashed:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(hash) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: and no entry: one that gives an entry is refused
# EZ-WS-5
law member_dep_entried:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(entry) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: and no source: one that names a directory is refused
# EZ-WS-5
law member_dep_pathed:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(path) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: or a name to import it by
# EZ-WS-5
law member_dep_nv:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(nv) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: every other dependency is left as it is written: a hub one
# EZ-WS-5
law member_dep_hub:
  for +name: String
  for +hash: String
  for +entry: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  {J.dep.res(M.Dep{name, hash, entry, M.Hub{nv}}, ms, self, files)
    == J.Got{M.Dep{name, hash, entry, M.Hub{nv}}} : J.Res}

# LAW: and a git one
# EZ-WS-5
law member_dep_git:
  for +name: String
  for +hash: String
  for +entry: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for vend: Bool
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  {J.dep.res(M.Dep{name, hash, entry, M.Git{url, rev, tag, root, nar, vend}}, ms, self, files)
    == J.Got{M.Dep{name, hash, entry, M.Git{url, rev, tag, root, nar, vend}}} : J.Res}

# LAW: a refused section refuses its ledger's dependencies, the first in the
# order written
# EZ-WS-5
law deps_res_refuses:
  for +dd: M.Dep
  for +ds: List<&2, M.Dep>
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +why: String
  for eb: {J.dep.res(dd, ms, self, files) == J.Bad{why} : J.Res}
  {J.deps.res(dd <> ds, ms, self, files) == J.Unmet{why} : J.Deps}

# LAW: a member whose dependencies are refused leaves the members unread
# EZ-WS-5
law res_one_refuses:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for rest: J.Read
  for +why: String
  for eu: {J.deps.res(J.deps.of(mm), ms, dir, files) == J.Unmet{why} : J.Deps}
  {J.res.one(J.Member{dir, mm}, ms, files, rest) == J.Unread{why} : J.Read}

# LAW: and so does any later member's refusal
# EZ-WS-5
law res_one_keeps_refusal:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for +ds: List<&2, M.Dep>
  for +why: String
  for eu: {J.deps.res(J.deps.of(mm), ms, dir, files) == J.Deps{ds} : J.Deps}
  {J.res.one(J.Member{dir, mm}, ms, files, J.Unread{why}) == J.Unread{why} : J.Read}

# LAW: members left unread leave nothing to lock: the joint ledger is refused
# with why
# EZ-WS-5
law resolve_refuses:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for +why: String
  for eu: {J.res.all(J.with.root(root, ms), J.with.root(root, ms), files) == J.Unread{why} : J.Read}
  {J.resolve(root, ms, files) == J.Clash{why} : J.Joint}

# LAW: and members resolved are joined as the ledgers they resolve to, every
# member imported by name a dependency after the root's own
# EZ-WS-5
# EZ-WS-6
law resolve_joins:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for dir: List<&2, String>
  for +rr: M.Manifest
  for +xs: List<&2, J.Member>
  for +ns: List<&2, M.Dep>
  for eu: {J.res.all(J.with.root(root, ms), J.with.root(root, ms), files) == J.Read{J.Member{dir, rr} <> xs}
    : J.Read}
  for en: {J.names.deps(J.with.root(root, ms), files) == J.Deps{ns} : J.Deps}
  {J.resolve(root, ms, files) == J.combine(J.with.deps(rr, List.append(&2, M.Dep, J.deps.of(rr), ns)), xs)
    : J.Joint}

# LAW: a member imported by name is a dependency of the joint ledger whether
# or not a section names it
# EZ-WS-6
law names_deps_named:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +xs: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for +nv: String
  for +dd: M.Dep
  for +ds: List<&2, M.Dep>
  for en: {J.member.naming(J.Member{dir, mm}) == PP.ByName{nv} : PP.Named}
  for eg: {J.member.dep(mm, dir, J.member.name(J.Member{dir, mm}), files) == J.Got{dd} : J.Res}
  for er: {J.names.deps(xs, files) == J.Deps{ds} : J.Deps}
  {J.names.deps(J.Member{dir, mm} <> xs, files) == J.Deps{dd <> ds} : J.Deps}

# LAW: and a member imported by its hash adds none
# EZ-WS-6
law names_deps_hashed:
  for +hd: J.Member
  for +xs: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for en: {J.member.naming(hd) == PP.ByHash{} : PP.Named}
  {J.names.deps(hd <> xs, files) == J.names.deps(xs, files) : J.Deps}

# LAW: the lock's name table holds a named member's name with its hash, as it
# holds a name ez.toml records, so the lock resolves it from the ledger
# (`ledger_names_first`) and never asks the hub or the lock being rewritten
# for it (`resolved_not_asked`)
# EZ-WS-6
law member_name_recorded:
  for +nn: String
  for +hash: String
  for entry: String
  for path: String
  for +nv: String
  for en: {String.is_empty(nv) == False{} : Bool}
  {L.ledger.names.of([M.Dep{nn, hash, entry, M.Member{path, nv}}]) == [L.Name{nv, hash}] : List<&2, L.Name>}

# LAW: the lock reads a member's package as its walk found it, fresh from the
# committed files: one answer, under the hash the joint ledger gives it
# EZ-WS-5
law seed_walked:
  for nn: String
  for +hash: String
  for +entry: String
  for +path: String
  for nv: String
  for +files: List<&2, K.Source>
  for hw: String
  for rw: String
  for +fs: List<&2, K.Source>
  for +sums: List<&2, K.Item>
  for ew: {K.of(entry, files) == K.Walked{hw, rw, fs, sums} : K.Walked}
  {J.seed(M.Dep{nn, hash, entry, M.Member{path, nv}}, files)
    == [LW.Reply{LW.Pkg{hash, L.Member{path, entry}, ""},
      LW.Got{LW.Clone{""}, K.manifest_of(sums), J.texts(sums, fs)}}] : List<&2, LW.Reply>}

# LAW: an answer read fresh is one the lock lays, as a clone's is
# EZ-WS-5
law seed_cloned:
  for +hash: String
  for src: L.Src
  for hub: String
  for nar: String
  for manifest: String
  for ss: List<&2, String>
  {LP.cloned([LW.Reply{LW.Pkg{hash, src, hub}, LW.Got{LW.Clone{nar}, manifest, ss}}]) == [hash]
    : List<&2, String>}

# LAW: the lock takes a member's dependency for a member's tree
# EZ-WS-5
law member_origin:
  for +nn: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  {L.ledger.origins([M.Dep{nn, hash, entry, M.Member{path, nv}}]) == [L.Origin{hash, L.Member{path, entry}}]
    : List<&2, L.Origin>}

# LAW: and judges its bytes alone, read fresh or from BEND_LIB
# EZ-WS-5
law member_judged:
  for path: String
  for entry: String
  for nar: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {LW.accept.src(L.Member{path, entry}, LW.Clone{nar}, hash, manifest, ss) == LW.body(hash, manifest, ss)
    : LW.Verdict}

# LAW: the same when it is read from BEND_LIB
# EZ-WS-5
law member_judged_lib:
  for path: String
  for entry: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {LW.accept.src(L.Member{path, entry}, LW.Lib{}, hash, manifest, ss) == LW.body(hash, manifest, ss)
    : LW.Verdict}

# LAW: the lock writes a member's source as its directory and entry, and reads
# it back
# EZ-WS-5
law member_src_reads:
  for +path: String
  for +entry: String
  {L.src_of(L.src.pairs(L.Member{path, entry})) == L.Member{path, entry} : L.Src}

# LAW: a member is never vendored, so it is never laid under `.ez/lib`
# EZ-WS-5
law member_not_vended:
  for nn: String
  for hash: String
  for entry: String
  for path: String
  for nv: String
  for +ds: List<&2, M.Dep>
  {I.vendors(M.Dep{nn, hash, entry, M.Member{path, nv}} <> ds) == I.vendors(ds) : List<&2, String>}

# LAW: a fresh tree that passed and is not vendored is laid under BEND_LIB at
# its hash
# EZ-WS-5
law member_laid:
  for +hash: String
  for +vs: List<&2, String>
  for fs: List<&2, K.Item>
  for ss: List<&2, String>
  for +rest: List<&2, LP.Effect>
  for ev: {L.seen.holds(vs, hash) == False{} : Bool}
  {LP.lays([hash], vs, [LW.Judged{hash, LW.Ok{fs, ss}}], rest)
    == LP.lay.verdict(LW.Ok{fs, ss}, LP.Cache{}, hash, rest) : List<&2, LP.Effect>}

# LAW: a member's section is no ledger's to record anything in: the upgrade
# writes it back as it was written
# EZ-WS-5
law member_back_kept:
  for +nn: String
  for +hash: String
  for +entry: String
  for path: String
  for nv: String
  for joint: M.Dep
  {U.dep.back.at(M.Dep{nn, hash, entry, M.Member{path, nv}}, joint) == M.Dep{nn, hash, entry, M.Member{path, nv}}
    : M.Dep}

# LAW: a `[deps.<name>]` section with `workspace = true` is never one missing
# its hash
# EZ-WS-5
law member_not_missing:
  for n: String
  for +ps: List<&2, T.Kv>
  for ew: {M.flag(M.value(ps, "workspace")) == True{} : Bool}
  {M.missing.is(T.Sect{n, ps}) == False{} : Bool}

# ---------------------------------------------------------------------------
# a member imported by its hash, once it moved (EZ-WS-7)

# LAW: a plain lock at a workspace root with a committed line naming the hash
# the lock being rewritten records for a member that has moved since refuses
# with why, writing nothing
# EZ-WS-7
law stale_plain_refuses:
  for +text: String
  for +spec: W.Spec
  for +fs: List<&2, J.Found>
  for +lock: String
  for +world: LW.World
  for +why: String
  for ev: {LW.args.upgrade(world) == False{} : Bool}
  for ew: {Mv.stale.world(lock, world) == why : String}
  for en: {String.is_empty(why) == False{} : Bool}
  {U.plan(U.Back{text, spec, fs, lock}, world) == LP.Plan{[], LP.Refused{why}} : LP.Plan}

# LAW: and it asks nothing first
# EZ-WS-7
law stale_plain_asks_nothing:
  for +text: String
  for +spec: W.Spec
  for +fs: List<&2, J.Found>
  for +lock: String
  for +world: LW.World
  for +why: String
  for ev: {LW.args.upgrade(world) == False{} : Bool}
  for ew: {Mv.stale.world(lock, world) == why : String}
  for en: {String.is_empty(why) == False{} : Bool}
  {U.step(U.Back{text, spec, fs, lock}, world) == LP.Run{LP.Plan{[], LP.Refused{why}}} : LP.Step}

# LAW: a file whose line names a moved member's recorded hash is the one the
# refusal names, with the member and the upgrade that rewrites the line
# EZ-WS-7
law stale_names_upgrade:
  for +name: String
  for +old: String
  for +new: String
  for rest: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for eh: {String.eq(LU.reimport.many([LU.Swap{old, new}], text), text) == False{} : Bool}
  {Mv.stale.moves(Mv.Shift{name, old, new} <> rest, at, text)
    == "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
      ", the hash the lock records for it, and the member is " ++ new ++
      " now; ez lock --upgrade --package " ++ name ++ " rewrites the import" : String}

# LAW: and a move no line of the file names is passed over
# EZ-WS-7
law stale_skips_move:
  for +name: String
  for +old: String
  for +new: String
  for +rest: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for eh: {String.eq(LU.reimport.many([LU.Swap{old, new}], text), text) == True{} : Bool}
  {Mv.stale.moves(Mv.Shift{name, old, new} <> rest, at, text) == Mv.stale.moves(rest, at, text) : String}

# LAW: the first committed file that names a moved member's recorded hash
# stops the lock
# EZ-WS-7
law stale_first_file:
  for +ms: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for +why: String
  for eh: {Mv.stale.moves(ms, at, text) == why : String}
  for en: {String.is_empty(why) == False{} : Bool}
  {Mv.stale(ms, K.Source{at, text} <> tl) == why : String}

# LAW: and a file that names none is passed over
# EZ-WS-7
law stale_skips_file:
  for +ms: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for eh: {Mv.stale.moves(ms, at, text) == "" : String}
  {Mv.stale(ms, K.Source{at, text} <> tl) == Mv.stale(ms, tl) : String}

# LAW: a member the lock records moves when its hash is not the one the lock
# records and it is chosen: every member for a plain lock and for an upgrade
# with no `--package`, the one named otherwise
# EZ-WS-7
law move_chosen:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for eo: {String.eq(new, old) == False{} : Bool}
  for ec: {LU.chosen(only, name) == True{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == Mv.Shift{name, old, new} <> rest
    : List<&2, Mv.Shift>}

# LAW: and so does one that is not chosen once the upgrade rewrote its files,
# which moved its hash from the one it had before any line was rewritten
# EZ-WS-7
law move_rewritten:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for eo: {String.eq(new, old) == False{} : Bool}
  for ec: {LU.chosen(only, name) == False{} : Bool}
  for eb: {String.eq(new, base) == False{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == Mv.Shift{name, old, new} <> rest
    : List<&2, Mv.Shift>}

# LAW: a member whose hash is the one the lock records does not move
# EZ-WS-7
law move_same:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for eo: {String.eq(new, old) == True{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == rest : List<&2, Mv.Shift>}

# LAW: nor does one not chosen whose files the upgrade did not rewrite
# EZ-WS-7
law move_untouched:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for ec: {LU.chosen(only, name) == False{} : Bool}
  for eb: {String.eq(new, base) == True{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == rest : List<&2, Mv.Shift>}

# LAW: a round of the upgrade rewrites every committed line naming a moved
# member's recorded hash, as an upgrade rewrites a moved dependency's
# (`LU.reimport.many`, EZ-VEN-2, EZ-VEN-3), from the files as they were
# EZ-WS-7
law rewrite_reimports:
  for +ss: List<&2, LU.Swap>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  {Mv.rewrite(ss, K.Source{at, text} <> tl) == K.Source{at, LU.reimport.many(ss, text)} <> Mv.rewrite(ss, tl)
    : List<&2, K.Source>}

# LAW: and walks every member again over them, for the moves the next round
# makes
# EZ-WS-7
law round_walks_again:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for +old: List<&2, Mv.Held>
  for +base: List<&2, Mv.Held>
  for +only: String
  for +ms: List<&2, Mv.Shift>
  {Mv.round(Mv.Ctx{text, fs, files, old, base, only}, ms)
    == Mv.moves(old, Mv.now(J.joint(text, fs, Mv.rewrite(Mv.swaps(ms), files))), base, only)
    : List<&2, Mv.Shift>}

# LAW: the rounds stop at the first that moves no member further
# EZ-WS-7
law cascade_stops:
  for fuel: Nat
  for +ctx: Mv.Ctx
  for +ms: List<&2, Mv.Shift>
  for es: {Mv.moves.eq(ms, Mv.round(ctx, ms)) == True{} : Bool}
  {Mv.cascade.go((1n + fuel : Nat), ctx, ms) == ms : List<&2, Mv.Shift>}

# LAW: and go on from one that does
# EZ-WS-7
law cascade_goes_on:
  for fuel: Nat
  for +ctx: Mv.Ctx
  for +ms: List<&2, Mv.Shift>
  for es: {Mv.moves.eq(ms, Mv.round(ctx, ms)) == False{} : Bool}
  {Mv.cascade.go((1n + fuel : Nat), ctx, ms) == Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms)) : List<&2, Mv.Shift>}

# LAW: an upgrade at a workspace root plans on the committed files rewritten
# with every move, the joint ledger and its members' answers made again over
# them
# EZ-WS-7
law up_plans_moved:
  for +text: String
  for spec: W.Spec
  for +fs: List<&2, J.Found>
  for +lock: String
  for +world: LW.World
  for ev: {LW.args.upgrade(world) == True{} : Bool}
  {U.plans.on(U.Back{text, spec, fs, lock}, world)
    == Mv.world.moved(
      J.joint(text, fs, Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, U.files.of(world), lock,
        LW.args.only(world)))), U.files.of(world))),
      Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, U.files.of(world), lock, LW.args.only(world)))),
        U.files.of(world)),
      world) : LW.World}

# LAW: and writes every committed file a move changes, with its lines
# rewritten
# EZ-WS-7
law edits_write_changed:
  for +ss: List<&2, LU.Swap>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for ec: {String.eq(LU.reimport.many(ss, text), text) == False{} : Bool}
  for el: {String.eq(at, LP.lockfile()) == False{} : Bool}
  {Mv.edits(ss, K.Source{at, text} <> tl) == LP.Write{at, LU.reimport.many(ss, text)} <> Mv.edits(ss, tl)
    : List<&2, LP.Effect>}

# LAW: and none it leaves as it was
# EZ-WS-7
law edits_skip_unchanged:
  for +ss: List<&2, LU.Swap>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for ec: {String.eq(LU.reimport.many(ss, text), text) == True{} : Bool}
  {Mv.edits(ss, K.Source{at, text} <> tl) == Mv.edits(ss, tl) : List<&2, LP.Effect>}

# ---------------------------------------------------------------------------
# `ez doctor` over a workspace (EZ-WS-9)

# LAW: for a project of its own, `ez doctor` makes the plan it always made
# EZ-WS-9
law doc_alone:
  for +world: DW.World
  {Doc.plan(Doc.Alone{}, world) == DP.plan(world) : LP.Plan}

# LAW: at a workspace root it judges the joint ledger, the text `ez lock`
# plans the root lock from, so the ledger, the lock, the library and the lock
# check (EZ-VEN-6) are judged over every member's ledger
# EZ-WS-9
law doc_judges_joint:
  for +mm: M.Manifest
  for +text: String
  for +fs: List<&2, J.Found>
  {Doc.joint(J.Joint{mm}, text, fs) == Doc.Doctored{J.joint.text(J.Joint{mm}, None{}), Doc.Back{text, fs, ""}}
    : Doc.Doctored}

# LAW: and says the doctor's own lines on it, with every member's report in
# place of the one drift report
# EZ-WS-9
law doc_lines:
  for +why: String
  for +text: String
  for +fs: List<&2, J.Found>
  for +world: DW.World
  {Doc.plan(Doc.Back{text, fs, why}, world)
    == DP.plan.notes(List.append(&2, DP.Note,
      DP.head.notes(DP.ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
        DW.replies(world), DP.checked(world)),
      Doc.tail(why, text, fs, world))) : LP.Plan}

# LAW: a member's report is over its own files, the ones under its directory
# EZ-WS-9
law doc_member_file:
  for +hd: String
  for +tl: List<&2, String>
  for +dirs: List<&2, List<&2, String>>
  for +at: String
  for text: String
  for +fs: List<&2, LW.Source>
  for eu: {Doc.under(W.segs.text(hd <> tl), at) == True{} : Bool}
  {Doc.own.files(hd <> tl, dirs, LW.Source{at, text} <> fs) == LW.Source{at, text} <> Doc.own.files(hd <> tl, dirs, fs)
    : List<&2, LW.Source>}

# LAW: and not over another's
# EZ-WS-9
law doc_other_file:
  for +hd: String
  for +tl: List<&2, String>
  for +dirs: List<&2, List<&2, String>>
  for +at: String
  for text: String
  for +fs: List<&2, LW.Source>
  for eu: {Doc.under(W.segs.text(hd <> tl), at) == False{} : Bool}
  {Doc.own.files(hd <> tl, dirs, LW.Source{at, text} <> fs) == Doc.own.files(hd <> tl, dirs, fs)
    : List<&2, LW.Source>}

# LAW: the root's report is over the files under no member's directory
# EZ-WS-9
law doc_root_file:
  for +dirs: List<&2, List<&2, String>>
  for +at: String
  for text: String
  for +fs: List<&2, LW.Source>
  for eu: {Doc.under.any(dirs, at) == False{} : Bool}
  {Doc.own.files([], dirs, LW.Source{at, text} <> fs) == LW.Source{at, text} <> Doc.own.files([], dirs, fs)
    : List<&2, LW.Source>}

# LAW: a member's report holds, in both directions, every hash its own import
# lines name that its own ledger does not, and every dependency of its ledger
# that none of them names (`DP.unrecorded`, `DP.unused`, EZ-VEN-5), each
# `workspace = true` section resolved to the member's package, and a member
# imported by its published name counting as named
# EZ-WS-9
law doc_member_drift:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +dirs: List<&2, List<&2, String>>
  for +nvs: List<&2, String>
  for +fs: List<&2, LW.Source>
  {Doc.member.drift(J.Member{dir, mm}, dirs, nvs, fs)
    == Doc.drift.notes(J.ledger.at(dir), DP.imports(Doc.own.files(dir, dirs, fs)),
      List.append(&2, String,
        DP.unrecorded(DP.missing(DP.imports(Doc.own.files(dir, dirs, fs)),
          List.append(&2, String, DP.pinned(J.deps.of(mm)), nvs))),
        DP.unused(J.deps.of(mm), DP.imports(Doc.own.files(dir, dirs, fs))))) : List<&2, DP.Note>}

# LAW: every line of a member's report is a problem, said for the member
# EZ-WS-9
law doc_drift_lines:
  for +place: String
  for hs: List<&2, String>
  for +ln: String
  for +ls: List<&2, String>
  {Doc.drift.notes(place, hs, ln <> ls) == DP.flag(Doc.at.lines(place, ln <> ls)) : List<&2, DP.Note>}

# LAW: a member whose package walks, from its entry over the committed files,
# to a hash the lock does not record for it at its directory is reported, as
# a problem
# EZ-WS-9
law doc_member_moved:
  for path: String
  for name: String
  for +held: String
  for +root: String
  for +now: String
  for en: {String.eq(now, held) == False{} : Bool}
  {Doc.moved.at(Some{Mv.Held{path, name, held}}, root, now) == [DP.Note{True{}, Doc.moved.line(root, now, held)}]
    : List<&2, DP.Note>}

# LAW: and one at the hash the lock records is not
# EZ-WS-9
law doc_member_same:
  for path: String
  for name: String
  for +held: String
  for +root: String
  for +now: String
  for en: {String.eq(now, held) == True{} : Bool}
  {Doc.moved.at(Some{Mv.Held{path, name, held}}, root, now) == [] : List<&2, DP.Note>}

# LAW: the walk is from the member's own entry over the committed files
# EZ-WS-9
law doc_member_walks:
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +files: List<&2, K.Source>
  for +locked: List<&2, Mv.Held>
  {Doc.member.moved(J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}, files, locked)
    == Doc.moved.walked(K.of(J.entry.at(dir, ee), files), locked) : List<&2, DP.Note>}

# LAW: `ez doctor` at a workspace root fails, so it exits 1, when any line it
# says is a problem
# EZ-WS-9
law doc_fails_on_problem:
  for +why: String
  for +text: String
  for +fs: List<&2, J.Found>
  for +world: DW.World
  for ew: {DP.wrong(Doc.notes(why, text, fs, world)) == True{} : Bool}
  {DP.refuses.plan(Doc.plan(Doc.Back{text, fs, why}, world)) == True{} : Bool}

# LAW: and passes when none is
# EZ-WS-9
law doc_passes_when_fine:
  for +why: String
  for +text: String
  for +fs: List<&2, J.Found>
  for +world: DW.World
  for ew: {DP.wrong(Doc.notes(why, text, fs, world)) == False{} : Bool}
  {DP.refuses.plan(Doc.plan(Doc.Back{text, fs, why}, world)) == False{} : Bool}

# LAW: and it writes nothing
# EZ-WS-9
law doc_writes_nothing:
  for +back: Doc.Back
  for +world: DW.World
  {LP.writes(Doc.plan(back, world)) == False{} : Bool}
