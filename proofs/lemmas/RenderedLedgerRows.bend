# the tables and rows of a rendered ledger, as they read back
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/toml/toml.bend as T
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/pub/blurb.bend as B
import ./StringDropZero.bend as M1

# ---------------------------------------------------------------------------
# laws/WrittenLedgerReadsBack.bend's text layer, the ledger read back from
# the text eztoml writes, is trusted through eztoml's round trip (trusted in
# src/toml/toml.bend, `ReadsBack`). What is here is ez's side of the model:
# `M.build` finds in the tables the fields they were written from
# (`read_ledger`), since every row with no value is left out and every key
# is written once in its table (`value_keep`).

# a line of a rendered ledger: a key with its value quoted, or a key with its
# value written bare, as `vendor = true` is. Proof vocabulary.
type Row is Data:
  Q{key: String, val: String}
  B{key: String, val: String}

def row.key(r: Row) -> String:
  match r:
    case Q{k, _v}:
      k
    case B{k, _v}:
      k

def row.val(r: Row) -> String:
  match r:
    case Q{_k, v}:
      v
    case B{_k, v}:
      v

# the pair a row reads back as
def row.kv(r: Row) -> T.Kv:
  match r:
    case Q{k, v}:
      T.Kv{k, v}
    case B{k, v}:
      T.Kv{k, v}

# a row kept ahead of the rest, or dropped when its value is empty
def keep.put(empty: Bool, r: Row, rest: List<&2, Row>) -> List<&2, Row>:
  match empty:
    case True{}:
      rest
    case False{}:
      r <> rest

# the rows that are written: those with a value
def keep(rs: List<&2, Row>) -> List<&2, Row>:
  match rs:
    case []:
      []
    case +r <> t:
      keep.put(String.is_empty(row.val(r)), r, keep(t))

def rows.kvs(rs: List<&2, Row>) -> List<&2, T.Kv>:
  match rs:
    case []:
      []
    case h <> t:
      row.kv(h) <> rows.kvs(t)

# a table of a rendered ledger: its name and every row it may write. Proof
# vocabulary.
type RSect is Data:
  RSect{name: String, rows: List<&2, Row>}

# the table a table of rows reads back as
def sect.of(s: RSect) -> T.Sect:
  RSect{n, rs} = s
  T.Sect{n, rows.kvs(keep(rs))}

def sects.of(ss: List<&2, RSect>) -> List<&2, T.Sect>:
  match ss:
    case []:
      []
    case h <> t:
      sect.of(h) <> sects.of(t)

# ---------------------------------------------------------------------------
# a ledger as tables of rows

# the rows of the `[package]` table
def pkg.rows(n: String, e: String, b: String, h: String, pa: String, pv: String) -> List<&2, Row>:
  [Q{"name", n}, Q{"entry", e}, Q{"bin", b}, Q{"hub", h}, Q{"publish-as", pa}, Q{"version", pv}]

# the rows a source writes
def src.rows(s: M.Source) -> List<&2, Row>:
  match s:
    case M.Hub{named}:
      [Q{"hub", named}]
    case M.Git{url, rev, tag, root, nar, vend}:
      [Q{"git", url}, Q{"rev", rev}, Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
        B{"vendor", Rend.vendor.word(vend)}]
    case M.Member{path, named}:
      [B{"workspace", "true"}, Q{"path", path}, Q{"hub", named}]

# the rows of a `[deps.<name>]` table
def dep.rows(h: String, e: String, s: M.Source) -> List<&2, Row>:
  Q{"hash", h} <> List.append(&2, Row, src.rows(s), [Q{"entry", e}])

# the rows of a `[tools.<name>]` table
def tool.rows(e: String, b: String, s: M.Source) -> List<&2, Row>:
  List.append(&2, Row, src.rows(s), [Q{"entry", e}, Q{"bin", b}])

def dep.sect(d: M.Dep) -> RSect:
  M.Dep{n, h, e, s} = d
  RSect{"deps." ++ n, dep.rows(h, e, s)}

def tool.sect(pin: M.Tool) -> RSect:
  M.Tool{n, e, b, s} = pin
  RSect{"tools." ++ n, tool.rows(e, b, s)}

def tsects(ts: List<&2, M.Tool>) -> List<&2, RSect>:
  match ts:
    case []:
      []
    case h <> t:
      tool.sect(h) <> tsects(t)

# every dependency's table, ahead of the tables given
def dsects(ds: List<&2, M.Dep>, rest: List<&2, RSect>) -> List<&2, RSect>:
  match ds:
    case []:
      rest
    case h <> t:
      dep.sect(h) <> dsects(t, rest)

# a ledger's tables, in the order the renderer writes them
def lsects(m: M.Manifest) -> List<&2, RSect>:
  M.Manifest{n, e, b, h, hpa, hpv, ds, ts} = m
  RSect{"package", pkg.rows(n, e, b, h, hpa, hpv)} <> dsects(ds, tsects(ts))

# LAW: an empty string is the empty string
law empty_is:
  for +s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {s == "" : String}

def empty_is(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Eq.bit.absurd(&2, {SCon{c, t} == "" : String}, e)

# ---------------------------------------------------------------------------
# what the reader finds in a renderable ledger's tables

# whether no row has a key. Proof vocabulary.
def rows.none(rs: List<&2, Row>, +k: String) -> Bool:
  match rs:
    case []:
      True{}
    case r <> t:
      rest = rows.none(t, k)
      Bool.and(Bool.not(String.eq(row.key(r), k)), rest)

# whether at most one row has a key
def rows.once(rs: List<&2, Row>, +k: String) -> Bool:
  match rs:
    case []:
      True{}
    case r <> +t:
      Bool.pick(Bool, String.eq(row.key(r), k), rows.none(t, k), rows.once(t, k))

# LAW: a row's pair answers a lookup with its value when the key is its own
law value_at_row:
  for +r: Row
  for rest: String
  for +k: String
  {T.value.at(row.kv(r), rest, k) == Bool.pick(String, String.eq(row.key(r), k), row.val(r), rest)
    : String}

def value_at_row(r, _rest, _k):
  match r:
    case Q{_k, _v}:
      {==}
    case B{_k, _v}:
      {==}

# LAW: rows none of which has a key answer it with nothing
law none_value:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.none(rs, k) == True{} : Bool}
  {T.value(rows.kvs(rs), k) == "" : String}

def none_value(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      +nk = Eq.not.true(String.eq(row.key(r), k),
        Eq.and.left(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(t), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(t), k)),
        value_at_row(r, T.value(rows.kvs(t), k), k))
        : {_ == "" : String}
      %Equal.sym(Bool, String.eq(row.key(r), k), False{}, nk)
        : {Bool.pick(String, _, row.val(r), T.value(rows.kvs(t), k)) == "" : String}
      none_value(t, k, Eq.and.right(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))

# LAW: one row, kept or dropped, with whether its value is empty given
law none_keep.arm:
  for +r: Row
  for +t: List<&2, Row>
  for +k: String
  for c: Bool
  for ek: {Bool.not(String.eq(row.key(r), k)) == True{} : Bool}
  for ih: {rows.none(keep(t), k) == True{} : Bool}
  {rows.none(keep.put(c, r, keep(t)), k) == True{} : Bool}

def none_keep.arm(r, t, k, c, ek, ih):
  match c:
    case True{}:
      ih
    case False{}:
      Str.and_true(Bool.not(String.eq(row.key(r), k)), rows.none(keep(t), k), ek, ih)

# LAW: and so do the rows kept of them
law none_keep:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.none(rs, k) == True{} : Bool}
  {rows.none(keep(rs), k) == True{} : Bool}

def none_keep(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      none_keep.arm(r, t, k, String.is_empty(row.val(r)),
        Eq.and.left(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e),
        none_keep(t, k, Eq.and.right(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e)))

# LAW: rows none of which has a key have it at most once
law none_once:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.none(rs, k) == True{} : Bool}
  {rows.once(rs, k) == True{} : Bool}

def none_once(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      +nk = Eq.not.true(String.eq(row.key(r), k),
        Eq.and.left(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))
      %Equal.sym(Bool, String.eq(row.key(r), k), False{}, nk)
        : {Bool.pick(Bool, _, rows.none(t, k), rows.once(t, k)) == True{} : Bool}
      none_once(t, k, Eq.and.right(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))

# LAW: the rows after one that has a key at most once have it at most once,
# with whether the first has it given
law once_tail.arm:
  for +t: List<&2, Row>
  for +k: String
  for b: Bool
  for e: {Bool.pick(Bool, b, rows.none(t, k), rows.once(t, k)) == True{} : Bool}
  {rows.once(t, k) == True{} : Bool}

def once_tail.arm(t, k, b, e):
  match b:
    case True{}:
      none_once(t, k, e)
    case False{}:
      e

# LAW: rows that have a key at most once, with the ones that have no value
# dropped, answer it as the rows do
law value_keep.arm:
  for +r: Row
  for +t: List<&2, Row>
  for +k: String
  for c: Bool
  for ec: {String.is_empty(row.val(r)) == c : Bool}
  for b: Bool
  for eb: {String.eq(row.key(r), k) == b : Bool}
  for e: {Bool.pick(Bool, b, rows.none(t, k), rows.once(t, k)) == True{} : Bool}
  for ih: {T.value(rows.kvs(keep(t)), k) == T.value(rows.kvs(t), k) : String}
  {T.value(rows.kvs(keep.put(c, r, keep(t))), k)
    == Bool.pick(String, b, row.val(r), T.value(rows.kvs(t), k)) : String}

def value_keep.arm(r, t, k, c, ec, b, eb, e, ih):
  match c b:
    case True{} True{}:
      Equal.trans(String, T.value(rows.kvs(keep(t)), k), "", row.val(r),
        none_value(keep(t), k, none_keep(t, k, e)),
        Equal.sym(String, row.val(r), "", empty_is(row.val(r), ec)))
    case True{} False{}:
      ih
    case False{} True{}:
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(keep(t)), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(keep(t)), k)),
        value_at_row(r, T.value(rows.kvs(keep(t)), k), k))
        : {_ == row.val(r) : String}
      %Equal.sym(Bool, String.eq(row.key(r), k), True{}, eb)
        : {Bool.pick(String, _, row.val(r), T.value(rows.kvs(keep(t)), k)) == row.val(r) : String}
      {==}
    case False{} False{}:
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(keep(t)), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(keep(t)), k)),
        value_at_row(r, T.value(rows.kvs(keep(t)), k), k))
        : {_ == T.value(rows.kvs(t), k) : String}
      %Equal.sym(Bool, String.eq(row.key(r), k), False{}, eb)
        : {Bool.pick(String, _, row.val(r), T.value(rows.kvs(keep(t)), k))
          == T.value(rows.kvs(t), k) : String}
      ih

# LAW: rows that have a key at most once answer it, once the rows with no
# value are dropped, as they did before
law value_keep:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.once(rs, k) == True{} : Bool}
  {T.value(rows.kvs(keep(rs)), k) == T.value(rows.kvs(rs), k) : String}

def value_keep(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(t), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(t), k)),
        value_at_row(r, T.value(rows.kvs(t), k), k))
        : {T.value(rows.kvs(keep(r <> t)), k) == _ : String}
      value_keep.arm(r, t, k, String.is_empty(row.val(r)), {==},
        String.eq(row.key(r), k), {==}, e,
        value_keep(t, k, once_tail.arm(t, k, String.eq(row.key(r), k), e)))

# LAW: two tables that answer a source's six keys alike are read as the same
# source
law source_same:
  for +ps: List<&2, T.Kv>
  for +qs: List<&2, T.Kv>
  for e1: {M.value(ps, "git") == M.value(qs, "git") : String}
  for e2: {M.value(ps, "rev") == M.value(qs, "rev") : String}
  for e3: {M.value(ps, "tag") == M.value(qs, "tag") : String}
  for e4: {M.value(ps, "root") == M.value(qs, "root") : String}
  for e5: {M.value(ps, "narHash") == M.value(qs, "narHash") : String}
  for e6: {M.value(ps, "vendor") == M.value(qs, "vendor") : String}
  {M.source_of(ps) == M.source_of(qs) : M.Source}

def source_same(ps, qs, e1, e2, e3, e4, e5, e6):
  %Equal.sym(String, M.value(ps, "git"), M.value(qs, "git"), e1)
    : {M.source.go(String.is_empty(_), _, M.value(ps, "rev"), M.value(ps, "tag"),
        M.root.or(M.value(ps, "root")), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "rev"), M.value(qs, "rev"), e2)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), _, M.value(ps, "tag"),
        M.root.or(M.value(ps, "root")), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "tag"), M.value(qs, "tag"), e3)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"), _,
        M.root.or(M.value(ps, "root")), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "root"), M.value(qs, "root"), e4)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"),
        M.value(qs, "tag"), M.root.or(_), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "narHash"), M.value(qs, "narHash"), e5)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"),
        M.value(qs, "tag"), M.root.or(M.value(qs, "root")), _, M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "vendor"), M.value(qs, "vendor"), e6)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"),
        M.value(qs, "tag"), M.root.or(M.value(qs, "root")), M.value(qs, "narHash"), M.flag(_))
      == M.source_of(qs) : M.Source}
  {==}

# LAW: rows that have each of a source's keys at most once are read, once
# the rows with no value are dropped, as the same source
law src_keep:
  for +rs: List<&2, Row>
  for s: M.Source
  for o1: {rows.once(rs, "git") == True{} : Bool}
  for o2: {rows.once(rs, "rev") == True{} : Bool}
  for o3: {rows.once(rs, "tag") == True{} : Bool}
  for o4: {rows.once(rs, "root") == True{} : Bool}
  for o5: {rows.once(rs, "narHash") == True{} : Bool}
  for o6: {rows.once(rs, "vendor") == True{} : Bool}
  for es: {M.source_of(rows.kvs(rs)) == s : M.Source}
  {M.source_of(rows.kvs(keep(rs))) == s : M.Source}

def src_keep(rs, s, o1, o2, o3, o4, o5, o6, es):
  Equal.trans(M.Source, M.source_of(rows.kvs(keep(rs))), M.source_of(rows.kvs(rs)), s,
    source_same(rows.kvs(keep(rs)), rows.kvs(rs),
      value_keep(rs, "git", o1), value_keep(rs, "rev", o2), value_keep(rs, "tag", o3),
      value_keep(rs, "root", o4), value_keep(rs, "narHash", o5), value_keep(rs, "vendor", o6)),
    es)

# LAW: the vendor bit rendered reads back as the bit
law flag_word:
  for vend: Bool
  {M.flag(Rend.vendor.word(vend)) == vend : Bool}

def flag_word(vend):
  match vend:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a git source that names its repo and its root is read as itself
law git_source:
  for +url: String
  for rev: String
  for tag: String
  for +root: String
  for nar: String
  for vend: Bool
  for eu: {String.is_empty(url) == False{} : Bool}
  for er: {String.is_empty(root) == False{} : Bool}
  {M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, M.flag(Rend.vendor.word(vend)))
    == M.Git{url, rev, tag, root, nar, vend} : M.Source}

def git_source(url, rev, tag, root, nar, vend, eu, er):
  %Equal.sym(Bool, String.is_empty(url), False{}, eu)
    : {M.source.go(_, url, rev, tag, M.root.or(root), nar, M.flag(Rend.vendor.word(vend)))
      == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  %Equal.sym(Bool, String.is_empty(root), False{}, er)
    : {M.source.go(False{}, url, rev, tag, Bool.pick(String, _, ".", root), nar,
        M.flag(Rend.vendor.word(vend))) == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  %Equal.sym(Bool, M.flag(Rend.vendor.word(vend)), vend, flag_word(vend))
    : {M.source.go(False{}, url, rev, tag, root, nar, _)
      == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  {==}

# LAW: a dependency's table, as it reads back, is read as the dependency
law dep_read:
  for +n: String
  for +h: String
  for +en: String
  for +s: M.Source
  for ok: {Rend.dep.ok(M.Dep{n, h, en, s}) == True{} : Bool}
  {M.dep_of("deps." ++ n, rows.kvs(keep(dep.rows(h, en, s)))) == M.Dep{n, h, en, s} : M.Dep}

def dep_read(n, h, en, s, ok):
  match s:
    case M.Hub{+named}:
      +rs = dep.rows(h, en, M.Hub{named})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "workspace"), M.value(rows.kvs(rs), "workspace"),
        value_keep(rs, "workspace", {==}))
        : {M.Dep{String.drop(n, 0n), M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(keep(rs)), "entry"),
          M.source.ws(M.flag(_), M.value(rows.kvs(keep(rs)), "path"), M.value(rows.kvs(keep(rs)), "hub"),
            M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs)))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"),
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _,
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hub"), M.value(rows.kvs(rs), "hub"),
        value_keep(rs, "hub", {==}))
        : {M.Dep{String.drop(n, 0n), h, en, M.source.named(_, M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Hub{""},
        src_keep(rs, M.Hub{""}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))
        : {M.Dep{String.drop(n, 0n), h, en, M.source.named(named, _)} == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, M1.drop_zero_ledger(n))
        : {M.Dep{_, h, en, M.Hub{named}} == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = dep.rows(h, en, M.Git{url, rev, tag, root, nar, vend})
      +es = Eq.and.right(Rend.clean(en), Rend.source.ok(M.Git{url, rev, tag, root, nar, vend}),
        Eq.and.right(Bool.and(Rend.clean(n), Rend.hash.ok(M.Git{url, rev, tag, root, nar, vend}, h)),
          Bool.and(Rend.clean(en), Rend.source.ok(M.Git{url, rev, tag, root, nar, vend})), ok))
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(Rend.clean(url), Rend.clean(rev)),
          Bool.and(Rend.clean(tag), Bool.and(Rend.clean(root), Rend.clean(nar)))), es)
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "workspace"), M.value(rows.kvs(rs), "workspace"),
        value_keep(rs, "workspace", {==}))
        : {M.Dep{String.drop(n, 0n), M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(keep(rs)), "entry"),
          M.source.ws(M.flag(_), M.value(rows.kvs(keep(rs)), "path"), M.value(rows.kvs(keep(rs)), "hub"),
            M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs)))))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"),
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _,
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Git{url, rev, tag, root, nar, vend},
        src_keep(rs, M.Git{url, rev, tag, root, nar, vend}, {==}, {==}, {==}, {==}, {==}, {==},
          git_source(url, rev, tag, root, nar, vend,
            Eq.not.true(String.is_empty(url),
              Eq.and.left(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)),
            Eq.not.true(String.is_empty(root),
              Eq.and.right(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)))))
        : {M.Dep{String.drop(n, 0n), h, en, M.source.named(M.value(rows.kvs(keep(rs)), "hub"), _)}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, M1.drop_zero_ledger(n))
        : {M.Dep{_, h, en, M.Git{url, rev, tag, root, nar, vend}}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      {==}
    case M.Member{+path, +named}:
      +rs = dep.rows(h, en, M.Member{path, named})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "workspace"), M.value(rows.kvs(rs), "workspace"),
        value_keep(rs, "workspace", {==}))
        : {M.Dep{String.drop(n, 0n), M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(keep(rs)), "entry"),
          M.source.ws(M.flag(_), M.value(rows.kvs(keep(rs)), "path"), M.value(rows.kvs(keep(rs)), "hub"),
            M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs)))))} == M.Dep{n, h,
                en, M.Member{path, named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"),
          M.Member{M.value(rows.kvs(keep(rs)), "path"), M.value(rows.kvs(keep(rs)), "hub")}} == M.Dep{n, h, en,
              M.Member{path, named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _,
          M.Member{M.value(rows.kvs(keep(rs)), "path"), M.value(rows.kvs(keep(rs)), "hub")}} == M.Dep{n, h, en,
              M.Member{path, named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "path"), M.value(rows.kvs(rs), "path"),
        value_keep(rs, "path", {==}))
        : {M.Dep{String.drop(n, 0n), h, en, M.Member{_, M.value(rows.kvs(keep(rs)), "hub")}} == M.Dep{n, h, en,
            M.Member{path, named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hub"), M.value(rows.kvs(rs), "hub"),
        value_keep(rs, "hub", {==}))
        : {M.Dep{String.drop(n, 0n), h, en, M.Member{path, _}} == M.Dep{n, h, en, M.Member{path, named}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, M1.drop_zero_ledger(n))
        : {M.Dep{_, h, en, M.Member{path, named}} == M.Dep{n, h, en, M.Member{path, named}} : M.Dep}
      {==}

# LAW: a pinned CLI's table, as it reads back, is read as the pin
law tool_read:
  for +n: String
  for +en: String
  for +b: String
  for +s: M.Source
  for ok: {Rend.tool.ok(M.Tool{n, en, b, s}) == True{} : Bool}
  {M.tool_of("tools." ++ n, rows.kvs(keep(tool.rows(en, b, s)))) == M.Tool{n, en, b, s} : M.Tool}

def tool_read(n, en, b, s, ok):
  match s:
    case M.Hub{+named}:
      %Equal.sym(String, named, "", empty_is(named,
        Eq.and.right(Bool.and(Rend.clean(en), Rend.clean(b)), String.is_empty(named),
          Eq.and.right(Rend.clean(n), Bool.and(Bool.and(Rend.clean(en), Rend.clean(b)),
            String.is_empty(named)), ok))))
        : {M.tool_of("tools." ++ n, rows.kvs(keep(tool.rows(en, b, M.Hub{_}))))
          == M.Tool{n, en, b, M.Hub{_}} : M.Tool}
      +rs = tool.rows(en, b, M.Hub{""})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Tool{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "bin"), M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "bin"), M.value(rows.kvs(rs), "bin"),
        value_keep(rs, "bin", {==}))
        : {M.Tool{String.drop(n, 0n), en, _, M.source_of(rows.kvs(keep(rs)))} == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Hub{""},
        src_keep(rs, M.Hub{""}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))
        : {M.Tool{String.drop(n, 0n), en, b, _} == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      %Equal.sym(String, String.drop(n, 0n), n, M1.drop_zero_ledger(n))
        : {M.Tool{_, en, b, M.Hub{""}} == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = tool.rows(en, b, M.Git{url, rev, tag, root, nar, vend})
      +es = Eq.and.right(Bool.and(Rend.clean(en), Rend.clean(b)),
        Rend.source.ok(M.Git{url, rev, tag, root, nar, vend}),
        Eq.and.right(Rend.clean(n), Bool.and(Bool.and(Rend.clean(en), Rend.clean(b)),
          Rend.source.ok(M.Git{url, rev, tag, root, nar, vend})), ok))
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(Rend.clean(url), Rend.clean(rev)),
          Bool.and(Rend.clean(tag), Bool.and(Rend.clean(root), Rend.clean(nar)))), es)
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Tool{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "bin"), M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "bin"), M.value(rows.kvs(rs), "bin"),
        value_keep(rs, "bin", {==}))
        : {M.Tool{String.drop(n, 0n), en, _, M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Git{url, rev, tag, root, nar, vend},
        src_keep(rs, M.Git{url, rev, tag, root, nar, vend}, {==}, {==}, {==}, {==}, {==}, {==},
          git_source(url, rev, tag, root, nar, vend,
            Eq.not.true(String.is_empty(url),
              Eq.and.left(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)),
            Eq.not.true(String.is_empty(root),
              Eq.and.right(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)))))
        : {M.Tool{String.drop(n, 0n), en, b, _} == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      %Equal.sym(String, String.drop(n, 0n), n, M1.drop_zero_ledger(n))
        : {M.Tool{_, en, b, M.Git{url, rev, tag, root, nar, vend}}
          == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      {==}

    case M.Member{path, named}:
      Eq.bit.absurd(&2,
        {M.tool_of("tools." ++ n, rows.kvs(keep(tool.rows(en, b, M.Member{path, named}))))
          == M.Tool{n, en, b, M.Member{path, named}} : M.Tool},
        Eq.and.right(Bool.and(Rend.clean(en), Rend.clean(b)), Rend.tool.src.ok(M.Member{path, named}),
          Eq.and.right(Rend.clean(n), Bool.and(Bool.and(Rend.clean(en), Rend.clean(b)),
            Rend.tool.src.ok(M.Member{path, named})), ok)))

# LAW: pinned CLIs' tables hold no dependency
law tdeps_none:
  for +ts: List<&2, M.Tool>
  {M.deps(sects.of(tsects(ts))) == [] : List<&2, M.Dep>}

def tdeps_none(ts):
  match ts:
    case []:
      {==}
    case M.Tool{_n, _e, _b, _s} <> +t:
      tdeps_none(t)

# LAW: the dependencies' tables, ahead of the pinned CLIs', are read as the
# dependencies
law deps_read:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +e: {Rend.deps.ok(ds) == True{} : Bool}
  {M.deps(sects.of(dsects(ds, tsects(ts)))) == ds : List<&2, M.Dep>}

def deps_read(ds, ts, e):
  match ds:
    case []:
      tdeps_none(ts)
    case M.Dep{+n, +h, +en, +s} <> +t:
      +ps = rows.kvs(keep(dep.rows(h, en, s)))
      +rest = dsects(t, tsects(ts))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.deps.put(_, T.Sect{"deps." ++ n, ps}, M.deps(sects.of(rest)))
          == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      %Equal.sym(M.Dep, M.dep_of("deps." ++ n, ps), M.Dep{n, h, en, s},
        dep_read(n, h, en, s, Eq.and.left(Rend.dep.ok(M.Dep{n, h, en, s}), Rend.deps.ok(t), e)))
        : {_ <> M.deps(sects.of(rest)) == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      %Equal.sym(List<&2, M.Dep>, M.deps(sects.of(rest)), t,
        deps_read(t, ts, Eq.and.right(Rend.dep.ok(M.Dep{n, h, en, s}), Rend.deps.ok(t), e)))
        : {M.Dep{n, h, en, s} <> _ == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      {==}

# LAW: the dependencies' tables hold no pinned CLI
law dtools_skip:
  for +ds: List<&2, M.Dep>
  for +rest: List<&2, RSect>
  {M.tools(sects.of(dsects(ds, rest))) == M.tools(sects.of(rest)) : List<&2, M.Tool>}

def dtools_skip(ds, rest):
  match ds:
    case []:
      {==}
    case M.Dep{_n, _h, _e, _s} <> +t:
      dtools_skip(t, rest)

# LAW: the pinned CLIs' tables are read as the pins
law tsects_read:
  for +ts: List<&2, M.Tool>
  for +e: {Rend.tools.ok(ts) == True{} : Bool}
  {M.tools(sects.of(tsects(ts))) == ts : List<&2, M.Tool>}

def tsects_read(ts, e):
  match ts:
    case []:
      {==}
    case M.Tool{+n, +en, +b, +s} <> +t:
      +ps = rows.kvs(keep(tool.rows(en, b, s)))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.tools.put(_, T.Sect{"tools." ++ n, ps}, M.tools(sects.of(tsects(t))))
          == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      %Equal.sym(M.Tool, M.tool_of("tools." ++ n, ps), M.Tool{n, en, b, s},
        tool_read(n, en, b, s, Eq.and.left(Rend.tool.ok(M.Tool{n, en, b, s}), Rend.tools.ok(t), e)))
        : {_ <> M.tools(sects.of(tsects(t))) == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      %Equal.sym(List<&2, M.Tool>, M.tools(sects.of(tsects(t))), t,
        tsects_read(t, Eq.and.right(Rend.tool.ok(M.Tool{n, en, b, s}), Rend.tools.ok(t), e)))
        : {M.Tool{n, en, b, s} <> _ == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      {==}

# LAW: pinned CLIs' tables miss no hash
law tmissing:
  for +ts: List<&2, M.Tool>
  {M.missing(sects.of(tsects(ts))) == "" : String}

def tmissing(ts):
  match ts:
    case []:
      {==}
    case M.Tool{_n, _e, _b, _s} <> +t:
      tmissing(t)

# LAW: a dependency's table that can be written is not one missing its hash:
# it names a workspace member, or it has one
law dep_kept:
  for +h: String
  for +en: String
  for +s: M.Source
  for +e: {Rend.hash.ok(s, h) == True{} : Bool}
  {Bool.and(Bool.not(M.flag(M.value(rows.kvs(keep(dep.rows(h, en, s))), "workspace"))),
    String.is_empty(M.value(rows.kvs(keep(dep.rows(h, en, s))), "hash"))) == False{} : Bool}

def dep_kept(h, en, s, e):
  match s:
    case M.Hub{+named}:
      +rs = dep.rows(h, en, M.Hub{named})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "workspace"), M.value(rows.kvs(rs), "workspace"),
        value_keep(rs, "workspace", {==}))
        : {Bool.and(Bool.not(M.flag(_)), String.is_empty(M.value(rows.kvs(keep(rs)), "hash"))) == False{} : Bool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {Bool.and(True{}, String.is_empty(_)) == False{} : Bool}
      Eq.not.true(String.is_empty(h), Eq.and.left(Bool.not(String.is_empty(h)), Rend.clean(h), e))
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = dep.rows(h, en, M.Git{url, rev, tag, root, nar, vend})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "workspace"), M.value(rows.kvs(rs), "workspace"),
        value_keep(rs, "workspace", {==}))
        : {Bool.and(Bool.not(M.flag(_)), String.is_empty(M.value(rows.kvs(keep(rs)), "hash"))) == False{} : Bool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {Bool.and(True{}, String.is_empty(_)) == False{} : Bool}
      Eq.not.true(String.is_empty(h), Eq.and.left(Bool.not(String.is_empty(h)), Rend.clean(h), e))
    case M.Member{+path, +named}:
      +rs = dep.rows(h, en, M.Member{path, named})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "workspace"), M.value(rows.kvs(rs), "workspace"),
        value_keep(rs, "workspace", {==}))
        : {Bool.and(Bool.not(M.flag(_)), String.is_empty(M.value(rows.kvs(keep(rs)), "hash"))) == False{} : Bool}
      {==}

# LAW: the tables of dependencies that have hashes, ahead of the pins', miss
# no hash
law missing_read:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +e: {Rend.deps.ok(ds) == True{} : Bool}
  {M.missing(sects.of(dsects(ds, tsects(ts)))) == "" : String}

def missing_read(ds, ts, e):
  match ds:
    case []:
      tmissing(ts)
    case M.Dep{+n, +h, +en, +s} <> +t:
      +rs = dep.rows(h, en, s)
      +rest = dsects(t, tsects(ts))
      +l = Eq.and.left(Bool.and(Rend.clean(n), Rend.hash.ok(s, h)),
        Bool.and(Rend.clean(en), Rend.source.ok(s)),
        Eq.and.left(Rend.dep.ok(M.Dep{n, h, en, s}), Rend.deps.ok(t), e))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.missing.at(Bool.and(_, Bool.and(Bool.not(M.flag(M.value(rows.kvs(keep(rs)), "workspace"))),
          String.is_empty(M.value(rows.kvs(keep(rs)), "hash")))),
          "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      %Equal.sym(Bool, Bool.and(Bool.not(M.flag(M.value(rows.kvs(keep(rs)), "workspace"))),
          String.is_empty(M.value(rows.kvs(keep(rs)), "hash"))), False{},
        dep_kept(h, en, s, Eq.and.right(Rend.clean(n), Rend.hash.ok(s, h), l)))
        : {M.missing.at(_, "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      missing_read(t, ts, Eq.and.right(Rend.dep.ok(M.Dep{n, h, en, s}), Rend.deps.ok(t), e))

# LAW: a renderable ledger's tables are read as the ledger
law read_ledger:
  for +n: String
  for +en: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +edk: {Rend.deps.ok(ds) == True{} : Bool}
  for +etk: {Rend.tools.ok(ts) == True{} : Bool}
  {M.read("", sects.of(lsects(M.Manifest{n, en, b, h, hpa, hpv, ds, ts})))
    == M.Good{M.Manifest{n, en, b, h, hpa, hpv, ds, ts}} : M.Read}

def read_ledger(n, en, b, h, hpa, hpv, ds, ts, edk, etk):
  +p = pkg.rows(n, en, b, h, hpa, hpv)
  +d = dsects(ds, tsects(ts))
  +s = sects.of(lsects(M.Manifest{n, en, b, h, hpa, hpv, ds, ts}))
  +g = {M.Good{M.Manifest{n, en, b, h, hpa, hpv, ds, ts}} : M.Read}
  %Equal.sym(String, M.missing(sects.of(d)), "", missing_read(ds, ts, edk))
    : {M.read.go(String.is_empty(M.problem("", _)), M.problem("", _), s) == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "name"), M.value(rows.kvs(p), "name"),
    value_keep(p, "name", {==}))
    : {M.Good{M.Manifest{_, M.value(rows.kvs(keep(p)), "entry"), M.value(rows.kvs(keep(p)), "bin"),
      M.value(rows.kvs(keep(p)), "hub"), M.value(rows.kvs(keep(p)), "publish-as"), M.value(rows.kvs(keep(p)),
      "version"), M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "entry"), M.value(rows.kvs(p), "entry"),
    value_keep(p, "entry", {==}))
    : {M.Good{M.Manifest{n, _, M.value(rows.kvs(keep(p)), "bin"), M.value(rows.kvs(keep(p)), "hub"),
      M.value(rows.kvs(keep(p)), "publish-as"), M.value(rows.kvs(keep(p)), "version"), M.deps(sects.of(d)),
      M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "bin"), M.value(rows.kvs(p), "bin"),
    value_keep(p, "bin", {==}))
    : {M.Good{M.Manifest{n, en, _, M.value(rows.kvs(keep(p)), "hub"), M.value(rows.kvs(keep(p)), "publish-as"),
      M.value(rows.kvs(keep(p)), "version"), M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "hub"), M.value(rows.kvs(p), "hub"),
    value_keep(p, "hub", {==}))
    : {M.Good{M.Manifest{n, en, b, _, M.value(rows.kvs(keep(p)), "publish-as"), M.value(rows.kvs(keep(p)), "version"),
      M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "publish-as"), M.value(rows.kvs(p), "publish-as"),
    value_keep(p, "publish-as", {==}))
    : {M.Good{M.Manifest{n, en, b, h, _, M.value(rows.kvs(keep(p)), "version"), M.deps(sects.of(d)),
      M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "version"), M.value(rows.kvs(p), "version"),
    value_keep(p, "version", {==}))
    : {M.Good{M.Manifest{n, en, b, h, hpa, _, M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(List<&2, M.Dep>, M.deps(sects.of(d)), ds, deps_read(ds, ts, edk))
    : {M.Good{M.Manifest{n, en, b, h, hpa, hpv, _, M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(List<&2, M.Tool>, M.tools(sects.of(d)), ts,
    Equal.trans(List<&2, M.Tool>, M.tools(sects.of(d)), M.tools(sects.of(tsects(ts))), ts,
      dtools_skip(ds, tsects(ts)), tsects_read(ts, etk)))
    : {M.Good{M.Manifest{n, en, b, h, hpa, hpv, ds, _}} == g : M.Read}
  {==}
