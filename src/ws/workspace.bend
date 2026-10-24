# ws/workspace: which directories a workspace's root ledger makes members
# (EZ-WS-1). A root ledger's `[workspace]` table lists `members`, each a
# directory relative to the root or `<dir>/*`, every directory directly under
# `<dir>`, and `exclude`, directories taken back out. The design is
# docs/rfc/ez-workspaces.md.
#
# Everything here is pure. A path is read as its segments, the pieces
# between its `/`s, so a member, an entry and an exclusion are compared
# segment by segment and nothing is cut off the end of a string. What the
# member set is decided from is the root ledger's text and, for every ez.toml
# git lists under the root, the directory it is in, its `[package] name` and
# whether it has a `[workspace]` table of its own. The interpreter of each
# command that reads a workspace gathers those; it decides nothing.
import Base
import 0xc5d9d3e28b79ea98be22eb42c7e37802/main.bend as E
import ../toml/toml.bend as T

# a path, as the segments between its `/`s
def segs.of(+path: String) -> List<&2, String>:
  String.split(path, '/')

# a path's segments, written back with `/` between them
def segs.text(ss: List<&2, String>) -> String:
  String.join(ss, "/")

# a list of segments with one more in front, when there was a list
def cut.cons(+head: String, rest: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match rest:
    case None{}:
      None{}
    case Some{ds}:
      Some{head <> ds}

# the last segment, kept when it is the word and nothing otherwise
def cut.last(hit: Bool) -> Maybe<&2, List<&2, String>>:
  match hit:
    case True{}:
      Some{[]}
    case False{}:
      None{}

# the segments before the last, when the last is the word: `libs/*` cut at
# `*` is `libs`, and `cli/ez.toml` cut at `ez.toml` is `cli`. A path whose last
# segment is another word cuts to nothing.
def cut(ss: List<&2, String>, +word: String) -> Maybe<&2, List<&2, String>>:
  match ss:
    case []:
      None{}
    case +hd <> []:
      cut.last(String.eq(hd, word))
    case +hd <> tl:
      cut.cons(hd, cut(tl, word))

# ---------------------------------------------------------------------------
# entries

# one entry of `members`: a directory named as it is, or every directory
# directly under one, which `<dir>/*` names
type Entry is Data:
  Plain{dir: List<&2, String>}
  Under{dir: List<&2, String>}

# an entry, once it is known whether its last segment is `*`
def entry.go(under: Maybe<&2, List<&2, String>>, +ss: List<&2, String>) -> Entry:
  match under:
    case Some{ds}:
      Under{ds}
    case None{}:
      Plain{ss}

# an entry's segments read: `<dir>/*` is every directory under `<dir>`, and
# anything else is the directory it names
def entry.of(+ss: List<&2, String>) -> Entry:
  entry.go(cut(ss, "*"), ss)

# the directory an entry names, or the one it names the directories under
def entry.dir(entry: Entry) -> List<&2, String>:
  match entry:
    case Plain{ds}:
      ds
    case Under{ds}:
      ds

# an entry as it was written
def entry.text(entry: Entry) -> String:
  match entry:
    case Plain{ds}:
      segs.text(ds)
    case Under{ds}:
      segs.text(ds) ++ "/*"

# whether a segment can be part of a member's path: it is not empty, which a
# leading `/` or a `//` would make it, it is neither `.` nor `..`, which
# would name a directory by where it is from here, and it is not `*`, which
# only ends an entry
def seg.ok(+seg: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(seg)),
    Bool.and(Bool.not(String.eq(seg, ".")),
      Bool.and(Bool.not(String.eq(seg, "..")), Bool.not(String.eq(seg, "*")))))

# whether every segment can be part of a member's path
def segs.ok(ss: List<&2, String>) -> Bool:
  match ss:
    case []:
      True{}
    case +hd <> tl:
      rest = segs.ok(tl)
      Bool.and(seg.ok(hd), rest)

# whether a directory is one a workspace can name: it has a segment, and
# every segment is one a member's path can have
def dir.ok(+ss: List<&2, String>) -> Bool:
  Bool.and(Bool.not(List.is_empty(&2, String, ss)), segs.ok(ss))

# whether every entry names a directory a workspace can name
def entries.ok(es: List<&2, Entry>) -> Bool:
  match es:
    case []:
      True{}
    case +hd <> tl:
      rest = entries.ok(tl)
      Bool.and(dir.ok(entry.dir(hd)), rest)

# the first entry that names no directory a workspace can name, "" for none
def entries.bad(es: List<&2, Entry>) -> String:
  match es:
    case []:
      ""
    case +hd <> tl:
      rest = entries.bad(tl)
      Bool.pick(String, dir.ok(entry.dir(hd)), rest, entry.text(hd))

# ---------------------------------------------------------------------------
# matching a directory

# whether two paths are one, segment by segment
def segs.eq(as: List<&2, String>, bs: List<&2, String>) -> Bool:
  match as:
    case []:
      List.is_empty(&2, String, bs)
    case +ah <> at:
      match bs:
        case []:
          False{}
        case +bh <> bt:
          rest = segs.eq(at, bt)
          Bool.and(String.eq(ah, bh), rest)

# whether a path is exactly one segment
def one(ds: List<&2, String>) -> Bool:
  match ds:
    case []:
      False{}
    case _hd <> tl:
      List.is_empty(&2, String, tl)

# whether a directory is directly under another: the other's segments, then
# exactly one more
def under(ps: List<&2, String>, ds: List<&2, String>) -> Bool:
  match ps:
    case []:
      one(ds)
    case +ph <> pt:
      match ds:
        case []:
          False{}
        case +dh <> dt:
          rest = under(pt, dt)
          Bool.and(String.eq(ph, dh), rest)

# whether an entry names a directory
def hit(entry: Entry, +ds: List<&2, String>) -> Bool:
  match entry:
    case Plain{ps}:
      segs.eq(ps, ds)
    case Under{ps}:
      under(ps, ds)

# whether any entry names a directory
def listed(es: List<&2, Entry>, +ds: List<&2, String>) -> Bool:
  match es:
    case []:
      False{}
    case +hd <> tl:
      rest = listed(tl, ds)
      Bool.or(hit(hd, ds), rest)

# whether a list of paths holds one
def has(xs: List<&2, List<&2, String>>, +ds: List<&2, String>) -> Bool:
  match xs:
    case []:
      False{}
    case +hd <> tl:
      rest = has(tl, ds)
      Bool.or(segs.eq(hd, ds), rest)

# ---------------------------------------------------------------------------
# the member set

# what `[workspace]` says: its entries and the directories it excludes
type Spec is Data:
  Spec{members: List<&2, Entry>, exclude: List<&2, List<&2, String>>}

# the root's ledger: one with a `[package]` table is a member, under its
# name, and one with none is a virtual root, which holds the workspace and
# nothing to build
type Root is Data:
  Virtual{}
  Package{name: String}

# an ez.toml git lists under the root, other than the root's own: the
# directory it is in, its `[package] name`, and whether it has a
# `[workspace]` table of its own
type Ledger is Data:
  Ledger{dir: List<&2, String>, name: String, nested: Bool}

# the member set, or why there is none: whether the root is a member, and
# every other member's directory
type Members is Data:
  Refused{why: String}
  Members{root: Bool, dirs: List<&2, List<&2, String>>}

# a ledger's directory
def ledger.dir(ledger: Ledger) -> List<&2, String>:
  Ledger{ds, _n, _w} = ledger
  ds

# a ledger's package name
def ledger.name(ledger: Ledger) -> String:
  Ledger{_ds, nn, _w} = ledger
  nn

# whether a ledger has a `[workspace]` table of its own
def ledger.nested(ledger: Ledger) -> Bool:
  Ledger{_ds, _n, ww} = ledger
  ww

# the directory of every ledger, in order
def dirs.of(ls: List<&2, Ledger>) -> List<&2, List<&2, String>>:
  match ls:
    case []:
      []
    case +hd <> tl:
      ledger.dir(hd) <> dirs.of(tl)

# whether a directory is a member: an entry names it and no exclusion does
def chosen(+spec: Spec, +ds: List<&2, String>) -> Bool:
  Spec{es, ex} = spec
  Bool.and(listed(es, ds), Bool.not(has(ex, ds)))

# this ledger in front of the rest, when its directory is a member
def picks.put(keep: Bool, +ledger: Ledger, rest: List<&2, Ledger>) -> List<&2, Ledger>:
  match keep:
    case True{}:
      ledger <> rest
    case False{}:
      rest

# every ledger whose directory is a member, in the order git listed them
def picks(+spec: Spec, ls: List<&2, Ledger>) -> List<&2, Ledger>:
  match ls:
    case []:
      []
    case +hd <> tl:
      picks.put(chosen(spec, ledger.dir(hd)), hd, picks(spec, tl))

# whether an entry that names a directory as it is names one that holds a
# committed ez.toml. `<dir>/*` names whatever is there, none included.
def present.one(entry: Entry, +found: List<&2, List<&2, String>>) -> Bool:
  match entry:
    case Plain{ps}:
      has(found, ps)
    case Under{_ps}:
      True{}

# whether every entry naming a directory as it is names one that is there
def present(es: List<&2, Entry>, +found: List<&2, List<&2, String>>) -> Bool:
  match es:
    case []:
      True{}
    case +hd <> tl:
      rest = present(tl, found)
      Bool.and(present.one(hd, found), rest)

# the first entry naming a directory as it is that names none there, "" for
# none
def absent(es: List<&2, Entry>, +found: List<&2, List<&2, String>>) -> String:
  match es:
    case []:
      ""
    case +hd <> tl:
      rest = absent(tl, found)
      Bool.pick(String, present.one(hd, found), rest, entry.text(hd))

# whether no member's ledger has a `[workspace]` table of its own
def unnested(ls: List<&2, Ledger>) -> Bool:
  match ls:
    case []:
      True{}
    case +hd <> tl:
      rest = unnested(tl)
      Bool.and(Bool.not(ledger.nested(hd)), rest)

# the first member whose ledger has a `[workspace]` table, "" for none
def nested(ls: List<&2, Ledger>) -> String:
  match ls:
    case []:
      ""
    case +hd <> tl:
      rest = nested(tl)
      Bool.pick(String, ledger.nested(hd), segs.text(ledger.dir(hd)), rest)

# the package name of every ledger, in order
def names.of(ls: List<&2, Ledger>) -> List<&2, String>:
  match ls:
    case []:
      []
    case +hd <> tl:
      ledger.name(hd) <> names.of(tl)

# the package name of every member, the root's first when it is one
def names(root: Root, ls: List<&2, Ledger>) -> List<&2, String>:
  match root:
    case Virtual{}:
      names.of(ls)
    case Package{nn}:
      nn <> names.of(ls)

# whether a list of names holds one
def named(ns: List<&2, String>, +nn: String) -> Bool:
  match ns:
    case []:
      False{}
    case +hd <> tl:
      rest = named(tl, nn)
      Bool.or(String.eq(hd, nn), rest)

# whether no name is in the list twice
def distinct(ns: List<&2, String>) -> Bool:
  match ns:
    case []:
      True{}
    case +hd <> +tl:
      rest = distinct(tl)
      Bool.and(Bool.not(named(tl, hd)), rest)

# the first name in the list twice, "" for none
def twice(ns: List<&2, String>) -> String:
  match ns:
    case []:
      ""
    case +hd <> +tl:
      rest = twice(tl)
      Bool.pick(String, named(tl, hd), hd, rest)

# whether the root is a member
def root.member(root: Root) -> Bool:
  match root:
    case Virtual{}:
      False{}
    case Package{_nn}:
      True{}

# whether the workspace has a member set: every entry names a directory a
# workspace can name, every one naming a directory as it is names one with a
# committed ez.toml, no member is a workspace root of its own, and no two
# members have one package name
def ok(+spec: Spec, +root: Root, +ls: List<&2, Ledger>) -> Bool:
  Spec{es, _ex} = spec
  Bool.and(entries.ok(es),
    Bool.and(present(es, dirs.of(ls)),
      Bool.and(unnested(picks(spec, ls)), distinct(names(root, picks(spec, ls))))))

# why a workspace has no member set, said for the first thing found wrong
def why(+spec: Spec, +root: Root, +ls: List<&2, Ledger>) -> String:
  Spec{es, _ex} = spec
  +bad = entries.bad(es)
  +gone = absent(es, dirs.of(ls))
  +deep = nested(picks(spec, ls))
  +dup = twice(names(root, picks(spec, ls)))
  Bool.pick(String, String.is_empty(bad),
    Bool.pick(String, String.is_empty(gone),
      Bool.pick(String, String.is_empty(deep),
        "ez: two workspace members are both named " ++ dup,
        "ez: workspace member " ++ deep ++ " has a [workspace] table of its own"),
      "ez: workspace member " ++ gone ++ " has no committed ez.toml"),
    "ez: workspace member " ++ bad ++ " is not a directory under the root")

# the member set, once it is known whether there is one
def members.go(fine: Bool, +spec: Spec, +root: Root, +ls: List<&2, Ledger>) -> Members:
  match fine:
    case True{}:
      Members{root.member(root), dirs.of(picks(spec, ls))}
    case False{}:
      Refused{why(spec, root, ls)}

# the members of a workspace: the root when it has a package, and the
# directory of every ledger an entry names and no exclusion does, or why
# there are none
def members(+spec: Spec, +root: Root, +ls: List<&2, Ledger>) -> Members:
  members.go(ok(spec, root, ls), spec, root, ls)

# ---------------------------------------------------------------------------
# reading the ledgers

# what a ledger's text says of its workspace: nothing, a `[workspace]` table,
# or why the table could not be read
type Read is Data:
  Lone{}
  Bad{why: String}
  Root{spec: Spec}

# every item of an array as text, or nothing when one is not a string
def strs(items: List<&2, E.Val>) -> Maybe<&2, List<&2, String>>:
  match items:
    case []:
      Some{[]}
    case E.VStr{text} <> tl:
      cut.cons(text, strs(tl))
    case E.VSpan{src, nn} <> tl:
      cut.cons(E.string(E.VSpan{src, nn}), strs(tl))
    case _hd <> tl:
      None{}

# a value read as an array of strings
def array.val(val: E.Val) -> Maybe<&2, List<&2, String>>:
  match val:
    case E.VArr{items}:
      strs(items)
    case _:
      None{}

# this pair's array when its key is the key, otherwise the rest's
def array.at(hit: Bool, val: E.Val, rest: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match hit:
    case True{}:
      array.val(val)
    case False{}:
      rest

# the array a table's key holds, an absent key holding none, or nothing when
# the key holds something else
def array(rows: List<&2, E.Val>, +key: String) -> Maybe<&2, List<&2, String>>:
  match rows:
    case []:
      Some{[]}
    case E.VPair{+name, val} <> tl:
      array.at(String.eq(name, key), val, array(tl, key))
    case _hd <> tl:
      array(tl, key)

# every text read as an entry
def entries.of(ts: List<&2, String>) -> List<&2, Entry>:
  match ts:
    case []:
      []
    case +hd <> tl:
      entry.of(segs.of(hd)) <> entries.of(tl)

# every text read as a path's segments
def paths.of(ts: List<&2, String>) -> List<&2, List<&2, String>>:
  match ts:
    case []:
      []
    case +hd <> tl:
      segs.of(hd) <> paths.of(tl)

# the table, once both arrays were read
def table.go(ms: Maybe<&2, List<&2, String>>, ex: Maybe<&2, List<&2, String>>) -> Read:
  match ms:
    case None{}:
      Bad{"ez: [workspace] members is not a list of strings"}
    case Some{mm}:
      match ex:
        case None{}:
          Bad{"ez: [workspace] exclude is not a list of strings"}
        case Some{xx}:
          Root{Spec{entries.of(mm), paths.of(xx)}}

# a `[workspace]` table's rows read
def table(+rows: List<&2, E.Val>) -> Read:
  table.go(array(rows, "members"), array(rows, "exclude"))

# this table when it is `[workspace]`, otherwise the rest's
def spec.at(hit: Bool, +sub: List<&2, E.Val>, rest: Read) -> Read:
  match hit:
    case True{}:
      table(sub)
    case False{}:
      rest

# the `[workspace]` table among a document's rows, or none
def spec.rows(rows: List<&2, E.Val>) -> Read:
  match rows:
    case []:
      Lone{}
    case E.VPair{+name, E.VHead{_path, +sub}} <> tl:
      spec.at(String.eq(name, "workspace"), sub, spec.rows(tl))
    case _hd <> tl:
      spec.rows(tl)

# what a ledger's text says of its workspace. A ledger that does not parse
# says nothing here; the command that reads it refuses it as it always has.
def spec.of(text: String) -> Read:
  spec.rows(E.root(E.parse(text)))

# a section's name
def sect.name(sect: T.Sect) -> String:
  T.Sect{nn, _ps} = sect
  nn

# whether a document has a section of this name
def sect.has(ss: List<&2, T.Sect>, +name: String) -> Bool:
  match ss:
    case []:
      False{}
    case +hd <> tl:
      rest = sect.has(tl, name)
      Bool.or(String.eq(sect.name(hd), name), rest)

# this section's pairs when its name matches, otherwise the rest's
def pairs.at(sect: T.Sect, rest: List<&2, T.Kv>, +name: String) -> List<&2, T.Kv>:
  T.Sect{nn, ps} = sect
  Bool.pick(List<&2, T.Kv>, String.eq(nn, name), ps, rest)

# the pairs of the section with this name, or none
def pairs.of(ss: List<&2, T.Sect>, +name: String) -> List<&2, T.Kv>:
  match ss:
    case []:
      []
    case hd <> tl:
      pairs.at(hd, pairs.of(tl, name), name)

# the root, read from its ledger's text: a member under its `[package] name`
# when it has a `[package]` table, a virtual root when it has none
def root.of(+text: String) -> Root:
  +ss = T.sects(T.parse(text))
  +nn = T.value(pairs.of(ss, "package"), "name")
  Bool.pick(Root, sect.has(ss, "package"), Package{nn}, Virtual{})

# a ledger under a directory of at least one segment
def ledger.some(ds: List<&2, String>, nn: String, ww: Bool) -> Maybe<&2, Ledger>:
  match ds:
    case []:
      None{}
    case +hd <> tl:
      Some{Ledger{hd <> tl, nn, ww}}

# the ledger, once its directory is known: the root's own ez.toml cuts to no
# segments, and is not one of these
def ledger.go(dir: Maybe<&2, List<&2, String>>, nn: String, ww: Bool) -> Maybe<&2, Ledger>:
  match dir:
    case None{}:
      None{}
    case Some{ds}:
      ledger.some(ds, nn, ww)

# a committed ez.toml under the root, read: the directory it is in, which is
# its path with the last segment cut, its `[package] name`, and whether it has
# a `[workspace]` table. A path that is not an ez.toml under a directory is
# none.
def ledger.of(+path: String, +text: String) -> Maybe<&2, Ledger>:
  +ss = T.sects(T.parse(text))
  ledger.go(cut(segs.of(path), "ez.toml"), T.value(pairs.of(ss, "package"), "name"),
    sect.has(ss, "workspace"))
