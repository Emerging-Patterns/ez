# A ledger with a `[workspace]` table is a workspace root. Its members are
# exactly the directories its `members` list names, less every directory
# `exclude` names, where an entry `<dir>/*` names every directory directly
# under `<dir>` that holds a committed ez.toml and any other entry names the
# directory it is written as. Every entry is a path relative to the root with
# at least one segment, and with no empty, `.`, `..` or `*` segment except the
# `*` that ends an entry. The root is a member too when its ledger has a
# `[package]` table. An entry that is not such a path, an entry naming a
# directory as it is with no committed ez.toml there, a member whose own
# ledger has a `[workspace]` table, and two members with the same `[package]
# name` are refused, and the command writes nothing.
#
# laws/WorkspaceMembersChosen.bend to laws/WorkspaceAddRemoveRelock.bend are
# proved over pure modules in `src/ws/` and the planners they feed, with the
# design in [docs/rfc/ez-workspaces.md](docs/rfc/ez-workspaces.md). The
# member set and the root are functions of the ledgers' texts and of git's
# answers (`src/ws/workspace.bend`, `src/ws/root.bend`). Every command that
# acts on the whole workspace plans on one joint ledger
# (`src/ws/joint.bend`), the root's package with every member's dependencies
# and tools, each `workspace = true` section resolved to the member's
# package walked over the committed files, and every member that publishes
# under a name a dependency by that name. So the lock planner's laws, which
# are about every World, hold of the workspace's one lock:
# laws/LockIdempotent.bend, laws/PlainLockKeepsLedger.bend,
# laws/HubNameResolvesToOneHash.bend and laws/ResolvedNotAsked.bend transfer
# unchanged (`lock_reproducible`, `plain_lock_writes_only_lock`,
# `ledger_names_first`, `resolved_not_asked`, each tagged for the workspace
# row it carries). What the lock planner does not see, it is given: the
# answers for each member's package, read fresh from the committed tree
# (`seed_walked`), and, under `--upgrade`, a World whose committed files the
# member moves already rewrote (`src/ws/moved.bend`, `up_plans_moved`). The
# write-back of moved pins into each member's ledger, the stale-hash refusal
# of a plain lock, `ez fetch`'s member trees, `ez doctor`'s per-member
# report, and the root's lock that `ez add` and `ez remove` write after
# their own plan (`src/ws/relock.bend`: the root lock planned over the
# ledgers they leave by `lock_root_plain`, each path it writes taken from
# the root by `at_write` and the laws beside it) are each a pure step around
# the existing planner, and the laws of each say what the step adds and that
# it leaves the rest as the planner made it. That the interpreter runs again
# at the root, reads each listed ez.toml, and reads the committed files as
# `ez lock` lists them is trusted in src/ez/app.bend.
#
# A workspace's member set is decided from the root ledger's `[workspace]`
# table and the ledgers git lists under the root, so what is stated here is
# that decision: an entry names a directory or every directory directly
# under one, a path that climbs or names itself by `.` is never one, and the
# members are exactly the listed directories no exclusion takes back, once
# nothing is refused.
import Base
import ../src/ws/workspace.bend as WWorkspace
import 0xc5d9d3e28b79ea98be22eb42c7e37802/main.bend as E
import ./defs/PathPrefix.bend as D1

# LAW: a path cut at its last segment, when that segment is the word, is the
# path before it. `libs/*` cut at `*` is `libs`, and `cli/ez.toml` cut at
# `ez.toml` is `cli`.
law cut_last:
  for +ds: List<&2, String>
  for +word: String
  {WWorkspace.cut(List.append(&2, String, ds, [word]), word) == Some{ds}
    : Maybe<&2, List<&2, String>>}

# LAW: an entry written `<dir>/*` names the directories under `<dir>`
law entry_under:
  for +ds: List<&2, String>
  {WWorkspace.entry.of(List.append(&2, String, ds, ["*"])) == WWorkspace.Under{ds} : WWorkspace.Entry}

# LAW: and any other entry names the directory it is written as
law entry_plain:
  for +ss: List<&2, String>
  for ev: {WWorkspace.cut(ss, "*") == None{} : Maybe<&2, List<&2, String>>}
  {WWorkspace.entry.of(ss) == WWorkspace.Plain{ss} : WWorkspace.Entry}

# LAW: a directory one segment below another is under it
law under_child:
  for +ps: List<&2, String>
  for +nn: String
  {WWorkspace.under(ps, List.append(&2, String, ps, [nn])) == True{} : Bool}

# LAW: and one two or more segments below it is not
law under_deeper:
  for +ps: List<&2, String>
  for nn: String
  for mm: String
  for rest: List<&2, String>
  {WWorkspace.under(ps, List.append(&2, String, ps, nn <> mm <> rest)) == False{} : Bool}

# LAW: a directory under another starts with the other's segments, so
# `<dir>/*` names nothing outside `<dir>`
law under_prefix:
  for ps: List<&2, String>
  for ds: List<&2, String>
  for +ev: {WWorkspace.under(ps, ds) == True{} : Bool}
  {D1.prefix(ps, ds) == True{} : Bool}

# LAW: a path with a segment no member's path may have is not one, wherever
# that segment stands
law segs_bad:
  for +ps: List<&2, String>
  for +bad: String
  for qs: List<&2, String>
  for ev: {WWorkspace.seg.ok(bad) == False{} : Bool}
  {WWorkspace.segs.ok(List.append(&2, String, ps, bad <> qs)) == False{} : Bool}

# LAW: an empty segment, which a leading `/` or a `//` makes, is refused
law seg_empty_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {WWorkspace.segs.ok(List.append(&2, String, ps, "" <> qs)) == False{} : Bool}

# LAW: and so is `.`
law seg_dot_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {WWorkspace.segs.ok(List.append(&2, String, ps, "." <> qs)) == False{} : Bool}

# LAW: and `..`, so no member climbs out of the root
law seg_up_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {WWorkspace.segs.ok(List.append(&2, String, ps, ".." <> qs)) == False{} : Bool}

# LAW: and a `*` anywhere but the end of an entry, which is no glob ez reads
law seg_star_refused:
  for +ps: List<&2, String>
  for qs: List<&2, String>
  {WWorkspace.segs.ok(List.append(&2, String, ps, "*" <> qs)) == False{} : Bool}

# LAW: an entry that names a directory names it wherever it stands among the
# entries
law listed_anywhere:
  for +fs: List<&2, WWorkspace.Entry>
  for ee: WWorkspace.Entry
  for es: List<&2, WWorkspace.Entry>
  for +ds: List<&2, String>
  for ev: {WWorkspace.hit(ee, ds) == True{} : Bool}
  {WWorkspace.listed(List.append(&2, WWorkspace.Entry, fs, ee <> es), ds) == True{} : Bool}

# LAW: an excluded directory is not a member, whatever names it
law excluded_not_chosen:
  for es: List<&2, WWorkspace.Entry>
  for +ex: List<&2, List<&2, String>>
  for +ds: List<&2, String>
  for ev: {WWorkspace.has(ex, ds) == True{} : Bool}
  {WWorkspace.chosen(WWorkspace.Spec{es, ex}, ds) == False{} : Bool}

# LAW: the members are exactly the ledgers' directories that an entry names
# and no exclusion does: every one of them, and nothing else
law picks_exactly:
  for +spec: WWorkspace.Spec
  for +ls: List<&2, WWorkspace.Ledger>
  for +ds: List<&2, String>
  {WWorkspace.has(WWorkspace.dirs.of(WWorkspace.picks(spec, ls)), ds)
    == Bool.and(WWorkspace.has(WWorkspace.dirs.of(ls), ds), WWorkspace.chosen(spec, ds)) : Bool}

# LAW: an entry naming a directory as it is, with no committed ez.toml there,
# leaves the workspace with no member set, wherever it stands
law present_anywhere:
  for +fs: List<&2, WWorkspace.Entry>
  for +ps: List<&2, String>
  for es: List<&2, WWorkspace.Entry>
  for +found: List<&2, List<&2, String>>
  for ev: {WWorkspace.has(found, ps) == False{} : Bool}
  {WWorkspace.present(List.append(&2, WWorkspace.Entry, fs, WWorkspace.Plain{ps} <> es), found) == False{} : Bool}

# LAW: a workspace with a member set has the root as a member exactly when its
# ledger has a package, and the picked directories as the rest
law members_when_ok:
  for +spec: WWorkspace.Spec
  for +root: WWorkspace.Root
  for +ls: List<&2, WWorkspace.Ledger>
  for ev: {WWorkspace.ok(spec, root, ls) == True{} : Bool}
  {WWorkspace.members(spec, root, ls) == WWorkspace.Members{WWorkspace.root.member(root),
      WWorkspace.dirs.of(WWorkspace.picks(spec, ls))}
    : WWorkspace.Members}

# LAW: and one with none is refused, with the reason why
law members_refused:
  for +spec: WWorkspace.Spec
  for +root: WWorkspace.Root
  for +ls: List<&2, WWorkspace.Ledger>
  for ev: {WWorkspace.ok(spec, root, ls) == False{} : Bool}
  {WWorkspace.members(spec, root, ls) == WWorkspace.Refused{WWorkspace.why(spec, root, ls)} : WWorkspace.Members}

# LAW: a member set is had only when every entry names a directory a
# workspace can name
law ok_needs_entries:
  for +es: List<&2, WWorkspace.Entry>
  for +ex: List<&2, List<&2, String>>
  for +root: WWorkspace.Root
  for +ls: List<&2, WWorkspace.Ledger>
  for +ev: {WWorkspace.ok(WWorkspace.Spec{es, ex}, root, ls) == True{} : Bool}
  {WWorkspace.entries.ok(es) == True{} : Bool}

# LAW: and every entry naming a directory as it is names one with a committed
# ez.toml
law ok_needs_present:
  for +es: List<&2, WWorkspace.Entry>
  for +ex: List<&2, List<&2, String>>
  for +root: WWorkspace.Root
  for +ls: List<&2, WWorkspace.Ledger>
  for +ev: {WWorkspace.ok(WWorkspace.Spec{es, ex}, root, ls) == True{} : Bool}
  {WWorkspace.present(es, WWorkspace.dirs.of(ls)) == True{} : Bool}

# LAW: and no member is a workspace root of its own
law ok_needs_unnested:
  for +spec: WWorkspace.Spec
  for +root: WWorkspace.Root
  for +ls: List<&2, WWorkspace.Ledger>
  for +ev: {WWorkspace.ok(spec, root, ls) == True{} : Bool}
  {WWorkspace.unnested(WWorkspace.picks(spec, ls)) == True{} : Bool}

# LAW: and no two members, the root among them, share a package name
law ok_needs_names:
  for +spec: WWorkspace.Spec
  for +root: WWorkspace.Root
  for +ls: List<&2, WWorkspace.Ledger>
  for +ev: {WWorkspace.ok(spec, root, ls) == True{} : Bool}
  {WWorkspace.distinct(WWorkspace.names(root, WWorkspace.picks(spec, ls))) == True{} : Bool}

# ---------------------------------------------------------------------------
# reading the `[workspace]` table (laws/WorkspaceMembersChosen.bend)

# LAW: the `[workspace]` table is found among a ledger's tables, wherever it
# stands after the ones before it
law spec_finds_table:
  for path: String
  for +sub: List<&2, E.Val>
  for rest: List<&2, E.Val>
  {WWorkspace.spec.rows(E.VPair{"workspace", E.VHead{path, sub}} <> rest) == WWorkspace.table(sub) : WWorkspace.Read}

# LAW: and a ledger whose tables hold none is no workspace root
law spec_none_lone:
  for path: String
  for sub: List<&2, E.Val>
  for +ch: Char
  for +tt: String
  for rest: List<&2, E.Val>
  for ev: {String.eq(SCon{ch, tt}, "workspace") == False{} : Bool}
  {WWorkspace.spec.rows(E.VPair{SCon{ch, tt}, E.VHead{path,
      sub}} <> rest) == WWorkspace.spec.rows(rest) : WWorkspace.Read}

# LAW: a table's entries and exclusions are the arrays its `members` and
# `exclude` keys hold, each text read as a path's segments
law table_reads:
  for +rows: List<&2, E.Val>
  for +ms: List<&2, String>
  for +xs: List<&2, String>
  for em: {WWorkspace.array(rows, "members") == Some{ms} : Maybe<&2, List<&2, String>>}
  for ex: {WWorkspace.array(rows, "exclude") == Some{xs} : Maybe<&2, List<&2, String>>}
  {WWorkspace.table(rows) == WWorkspace.Root{WWorkspace.Spec{WWorkspace.entries.of(ms),
      WWorkspace.paths.of(xs)}} : WWorkspace.Read}

# LAW: a `members` that is not an array of strings is refused, never read as
# a shorter list
law table_refuses_members:
  for +rows: List<&2, E.Val>
  for em: {WWorkspace.array(rows, "members") == None{} : Maybe<&2, List<&2, String>>}
  {WWorkspace.table(rows) == WWorkspace.Bad{"ez: [workspace] members is not a list of strings"} : WWorkspace.Read}

# LAW: a key's array is the strings it holds
law array_at_key:
  for +key: String
  for +items: List<&2, E.Val>
  for rest: List<&2, E.Val>
  {WWorkspace.array(E.VPair{key, E.VArr{items}} <> rest, key) == WWorkspace.strs(items) : Maybe<&2, List<&2, String>>}

# LAW: and an array holding anything but strings holds none
law strs_refuses_other:
  for bit: Bool
  for rest: List<&2, E.Val>
  {WWorkspace.strs(E.VBool{bit} <> rest) == None{} : Maybe<&2, List<&2, String>>}
