# ws: the laws. The human states them; PROOF.bend must prove them. A
# workspace's member set is decided from the root ledger's `[workspace]`
# table and the ledgers git lists under the root, so what is stated here is
# that decision: an entry names a directory or every directory directly under
# one, a path that climbs or names itself by `.` is never one, and the
# members are exactly the listed directories no exclusion takes back, once
# nothing is refused.
import Base
import ./workspace.bend as W

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
