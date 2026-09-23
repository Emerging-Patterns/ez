import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../check/toml.bend as TP

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

# the row's line, without its newline
def row.line(r: Row) -> String:
  match r:
    case Q{k, v}:
      TP.pair.line(T.Kv{k, v})
    case B{k, v}:
      k ++ " = " ++ v

# the row as the renderer writes it: nothing when its value is empty
def row.text(r: Row) -> String:
  match r:
    case Q{k, v}:
      R.line(k, v)
    case B{k, v}:
      R.line.bare(k, v)

# whether a row reads back as its pair: a quoted row's key is bare and holds
# no `=`, `"` or newline, and its value no newline; a bare row is `vendor =
# true`, or has no value and so is not written
def row.ok(r: Row) -> Bool:
  match r:
    case Q{+k, +v}:
      Bool.and(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
        Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))))
    case B{+k, +v}:
      Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true")))

def rows.ok(rs: List<&2, Row>) -> Bool:
  match rs:
    case []:
      True{}
    case h <> t:
      rest = rows.ok(t)
      Bool.and(row.ok(h), rest)

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

# the pairs a table being filled holds once a row is read, kept or dropped
def keep.acc(empty: Bool, r: Row, acc: List<&2, T.Kv>) -> List<&2, T.Kv>:
  match empty:
    case True{}:
      acc
    case False{}:
      row.kv(r) <> acc

def rows.lines(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case []:
      []
    case h <> t:
      row.line(h) <> rows.lines(t)

def rows.kvs(rs: List<&2, Row>) -> List<&2, T.Kv>:
  match rs:
    case []:
      []
    case h <> t:
      row.kv(h) <> rows.kvs(t)

def rows.text(rs: List<&2, Row>) -> String:
  match rs:
    case []:
      ""
    case h <> t:
      row.text(h) ++ rows.text(t)

# LAW: the one bare line a ledger holds, read into a table being filled, adds
# its pair
law step_vendor:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for en: {String.is_empty(n) == False{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, "vendor = true")
    == T.Toml{bad, n, T.Kv{"vendor", "true"} <> acc, done} : T.Toml}

def step_vendor(bad, n, acc, done, en):
  %Equal.sym(Bool, String.is_empty(n), False{}, en)
    : {T.put.go(_, bad, n, acc, done, "vendor", "true")
      == T.Toml{bad, n, T.Kv{"vendor", "true"} <> acc, done} : T.Toml}
  {==}

# LAW: a row with a value, read into a table being filled, adds its pair
law step_row:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +r: Row
  for en: {String.is_empty(n) == False{} : Bool}
  for ev: {String.is_empty(row.val(r)) == False{} : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, row.line(r))
    == T.Toml{bad, n, row.kv(r) <> acc, done} : T.Toml}

def step_row(bad, n, acc, done, r, en, ev, ok):
  match r:
    case Q{+k, +v}:
      +ok2 = Eq.and.right(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
        Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))), ok)
      TP.step_pair(bad, n, acc, done, k, v, en,
        Eq.and.left(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))), ok2),
        Eq.and.left(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')),
          Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
            Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))), ok2)))
    case B{+k, +v}:
      +ab = Equal.trans(Bool, Bool.and(String.eq(k, "vendor"), String.eq(v, "true")),
        Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
        True{},
        Equal.cong(Bool, Bool, x => Bool.or(x, Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
          False{}, String.is_empty(v), Equal.sym(Bool, String.is_empty(v), False{}, ev)),
        ok)
      ek = Str.string_eq_true(k, "vendor", Eq.and.left(String.eq(k, "vendor"), String.eq(v, "true"), ab))
      evv = Str.string_eq_true(v, "true", Eq.and.right(String.eq(k, "vendor"), String.eq(v, "true"), ab))
      %Equal.sym(String, k, "vendor", ek) : {T.step(T.Toml{bad, n, acc, done}, _ ++ " = " ++ v)
        == T.Toml{bad, n, T.Kv{_, v} <> acc, done} : T.Toml}
      %Equal.sym(String, v, "true", evv) : {T.step(T.Toml{bad, n, acc, done}, "vendor = " ++ _)
        == T.Toml{bad, n, T.Kv{"vendor", _} <> acc, done} : T.Toml}
      step_vendor(bad, n, acc, done, en)


# LAW: one row, kept or dropped, read into a table being filled, with whether
# its value is empty given as a parameter
law walk_rows.arm:
  for +r: Row
  for +t: List<&2, Row>
  for +rest: List<&2, String>
  for +bad: String
  for +n: String
  for +acc: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for b: Bool
  for eb: {String.is_empty(row.val(r)) == b : Bool}
  for +en: {String.is_empty(n) == False{} : Bool}
  for +ok: {row.ok(r) == True{} : Bool}
  for ih: {T.parse.walk(List.append(&2, String, rows.lines(keep(t)), rest),
      T.Toml{bad, n, keep.acc(b, r, acc), done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(t)),
      keep.acc(b, r, acc)), done}) : T.Toml}
  {T.parse.walk(List.append(&2, String, rows.lines(keep.put(b, r, keep(t))), rest),
      T.Toml{bad, n, acc, done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv,
      rows.kvs(keep.put(b, r, keep(t))), acc), done}) : T.Toml}

def walk_rows.arm(r, t, rest, bad, n, acc, done, b, eb, en, ok, ih):
  match b:
    case True{}:
      ih
    case False{}:
      s = Equal.sym(T.Toml, T.step(T.Toml{bad, n, acc, done}, row.line(r)),
        T.Toml{bad, n, row.kv(r) <> acc, done},
        step_row(bad, n, acc, done, r, en, eb, ok))
      %s : {T.parse.walk(List.append(&2, String, rows.lines(keep(t)), rest), _)
        == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv,
          rows.kvs(keep(t)), row.kv(r) <> acc), done}) : T.Toml}
      ih

# LAW: the rows a table writes, read into it, add their pairs, reversed
law walk_rows:
  for +rs: List<&2, Row>
  for +rest: List<&2, String>
  for +bad: String
  for +n: String
  for +acc: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +en: {String.is_empty(n) == False{} : Bool}
  for +eok: {rows.ok(rs) == True{} : Bool}
  {T.parse.walk(List.append(&2, String, rows.lines(keep(rs)), rest), T.Toml{bad, n, acc, done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), acc), done})
    : T.Toml}

# by induction on the rows, each one kept or dropped
def walk_rows(rs, rest, bad, n, acc, done, en, eok):
  match rs:
    case []:
      {==}
    case +r <> +t:
      walk_rows.arm(r, t, rest, bad, n, acc, done, String.is_empty(row.val(r)), {==}, en,
        Eq.and.left(row.ok(r), rows.ok(t), eok),
        walk_rows(t, rest, bad, n, keep.acc(String.is_empty(row.val(r)), r, acc), done, en,
          Eq.and.right(row.ok(r), rows.ok(t), eok)))

# a table of a rendered ledger: its name and every row it may write. Proof
# vocabulary.
type RSect is Data:
  RSect{name: String, rows: List<&2, Row>}

# the lines of a ledger: each table's header, the rows it writes, and a blank
# line
def rdoc.lines(ss: List<&2, RSect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case RSect{n, rs} <> t:
      TP.head.line(n) <> List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t))

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

# whether a table reads back: its name is not empty and holds no newline, and
# every row reads back
def rsect.ok(s: RSect) -> Bool:
  RSect{+n, rs} = s
  Bool.and(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)))

def rsects.ok(ss: List<&2, RSect>) -> Bool:
  match ss:
    case []:
      True{}
    case h <> t:
      rest = rsects.ok(t)
      Bool.and(rsect.ok(h), rest)

# LAW: a table's lines, read, fill it and file the one before it
law walk_rsect:
  for +n: String
  for +rs: List<&2, Row>
  for +t: List<&2, RSect>
  for +bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +en: {String.is_empty(n) == False{} : Bool}
  for +eok: {rows.ok(rs) == True{} : Bool}
  {T.parse.walk(rdoc.lines(RSect{n, rs} <> t), T.Toml{bad, name, pairs, done})
    == T.parse.walk(rdoc.lines(t),
      T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)})
    : T.Toml}

# the header, then the rows; the blank line changes nothing
def walk_rsect(n, rs, t, bad, name, pairs, done, en, eok):
  h = Equal.sym(T.Toml, T.step(T.Toml{bad, name, pairs, done}, TP.head.line(n)),
    T.Toml{bad, n, [], T.flush(name, pairs, done)}, TP.step_head(bad, name, pairs, done, n))
  %h : {T.parse.walk(List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)), _)
    == T.parse.walk(rdoc.lines(t),
      T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)})
    : T.Toml}
  walk_rows(rs, "" <> rdoc.lines(t), bad, n, [], T.flush(name, pairs, done), en, eok)

# LAW: a ledger's lines, read from any state with no error, file the tables
# it already filed and then every table the ledger holds
law walk_rdoc:
  for +ss: List<&2, RSect>
  for +bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +eok: {rsects.ok(ss) == True{} : Bool}
  {T.parse.fin(T.parse.walk(rdoc.lines(ss), T.Toml{bad, name, pairs, done}))
    == T.Toml{bad, "", [], List.append(&2, T.Sect,
      List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(ss))} : T.Toml}

# by induction on the tables
def walk_rdoc(ss, bad, name, pairs, done, eok):
  match ss:
    case []:
      Equal.cong(List<&2, T.Sect>, T.Toml, x => T.Toml{bad, "", [], x},
        List.reverse(&2, T.Sect, T.flush(name, pairs, done)),
        List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)), []),
        Equal.sym(List<&2, T.Sect>,
          List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)), []),
          List.reverse(&2, T.Sect, T.flush(name, pairs, done)),
          Str.list_append_nil(T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)))))
    case RSect{+n, +rs} <> +t:
      +ok = Eq.and.left(rsect.ok(RSect{n, rs}), rsects.ok(t), eok)
      +en = Eq.not.true(String.is_empty(n), Eq.and.left(Bool.not(String.is_empty(n)),
        Bool.and(Str.clear(n, '\n'), rows.ok(rs)), ok))
      ep = Eq.and.right(Str.clear(n, '\n'), rows.ok(rs),
        Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)), ok))
      w = Equal.sym(T.Toml,
        T.parse.walk(rdoc.lines(RSect{n, rs} <> t), T.Toml{bad, name, pairs, done}),
        T.parse.walk(rdoc.lines(t),
          T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)}),
        walk_rsect(n, rs, t, bad, name, pairs, done, en, ep))
      %w : {T.parse.fin(_) == T.Toml{bad, "", [], List.append(&2, T.Sect,
        List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(RSect{n, rs} <> t))} : T.Toml}
      Equal.trans(T.Toml,
        T.parse.fin(T.parse.walk(rdoc.lines(t),
          T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)})),
        T.Toml{bad, "", [], List.append(&2, T.Sect, List.reverse(&2, T.Sect,
          T.flush(n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done))),
          sects.of(t))},
        T.Toml{bad, "", [], List.append(&2, T.Sect,
          List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(RSect{n, rs} <> t))},
        walk_rdoc(t, bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []),
          T.flush(name, pairs, done), Eq.and.right(rsect.ok(RSect{n, rs}), rsects.ok(t), eok)),
        Equal.cong(List<&2, T.Sect>, T.Toml, x => T.Toml{bad, "", [], x},
          List.append(&2, T.Sect, List.reverse(&2, T.Sect,
            T.flush(n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done))),
            sects.of(t)),
          List.append(&2, T.Sect,
            List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(RSect{n, rs} <> t)),
          TP.flush_filed(n, rows.kvs(keep(rs)), T.flush(name, pairs, done), sects.of(t), en)))

# LAW: a bare row with a value that reads back is `vendor = true`
law vendor_row:
  for +k: String
  for +v: String
  for ev: {String.is_empty(v) == False{} : Bool}
  for ok: {Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true")))
    == True{} : Bool}
  {B{k, v} == B{"vendor", "true"} : Row}

# the `or`'s first half is False, so its second answered True
def vendor_row(k, v, ev, ok):
  +ab = Equal.trans(Bool, Bool.and(String.eq(k, "vendor"), String.eq(v, "true")),
    Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
    True{},
    Equal.cong(Bool, Bool, x => Bool.or(x, Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
      False{}, String.is_empty(v), Equal.sym(Bool, String.is_empty(v), False{}, ev)),
    ok)
  ek = Str.string_eq_true(k, "vendor", Eq.and.left(String.eq(k, "vendor"), String.eq(v, "true"), ab))
  evv = Str.string_eq_true(v, "true", Eq.and.right(String.eq(k, "vendor"), String.eq(v, "true"), ab))
  %Equal.sym(String, k, "vendor", ek) : {B{_, v} == B{"vendor", "true"} : Row}
  %Equal.sym(String, v, "true", evv) : {B{"vendor", _} == B{"vendor", "true"} : Row}
  {==}

# LAW: a row with a value that reads back writes a line with no newline
law row_clear:
  for +r: Row
  for ev: {String.is_empty(row.val(r)) == False{} : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  {Str.clear(row.line(r), '\n') == True{} : Bool}

def row_clear(r, ev, ok):
  match r:
    case Q{+k, +v}:
      +ok3 = Eq.and.right(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')),
        Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))),
          Eq.and.right(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
            Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))), ok)))
      Str.clear_append(T.key(k), " = " ++ T.quote(v), '\n',
        TP.key_clear.go(k, T.bare(k), Eq.and.left(Str.clear(k, '\n'), Str.clear(v, '\n'), ok3)),
        Str.clear_append(v, "\"", '\n',
          Eq.and.right(Str.clear(k, '\n'), Str.clear(v, '\n'), ok3), {==}))
    case B{+k, +v}:
      %Equal.sym(Row, B{k, v}, B{"vendor", "true"}, vendor_row(k, v, ev, ok))
        : {Str.clear(row.line(_), '\n') == True{} : Bool}
      {==}

# LAW: one row, kept or dropped, with whether its value is empty given
law rows_clear.arm:
  for +r: Row
  for +t: List<&2, Row>
  for b: Bool
  for eb: {String.is_empty(row.val(r)) == b : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  for ih: {Str.clear.all(rows.lines(keep(t)), '\n') == True{} : Bool}
  {Str.clear.all(rows.lines(keep.put(b, r, keep(t))), '\n') == True{} : Bool}

def rows_clear.arm(r, t, b, eb, ok, ih):
  match b:
    case True{}:
      ih
    case False{}:
      Str.and_true(Str.clear(row.line(r), '\n'), Str.clear.all(rows.lines(keep(t)), '\n'),
        row_clear(r, eb, ok), ih)

# LAW: no line a table's rows write holds a newline
law rows_clear:
  for +rs: List<&2, Row>
  for +eok: {rows.ok(rs) == True{} : Bool}
  {Str.clear.all(rows.lines(keep(rs)), '\n') == True{} : Bool}

def rows_clear(rs, eok):
  match rs:
    case []:
      {==}
    case +r <> +t:
      rows_clear.arm(r, t, String.is_empty(row.val(r)), {==},
        Eq.and.left(row.ok(r), rows.ok(t), eok),
        rows_clear(t, Eq.and.right(row.ok(r), rows.ok(t), eok)))

# LAW: no line of a ledger that reads back holds a newline
law rlines_clear:
  for +ss: List<&2, RSect>
  for +eok: {rsects.ok(ss) == True{} : Bool}
  {Str.clear.all(rdoc.lines(ss), '\n') == True{} : Bool}

# by induction on the tables
def rlines_clear(ss, eok):
  match ss:
    case []:
      {==}
    case RSect{+n, +rs} <> +t:
      +ok = Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)),
        Eq.and.left(rsect.ok(RSect{n, rs}), rsects.ok(t), eok))
      Str.and_true(Str.clear(TP.head.line(n), '\n'),
        Str.clear.all(List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)), '\n'),
        Str.clear_append(n, "]", '\n', Eq.and.left(Str.clear(n, '\n'), rows.ok(rs), ok), {==}),
        Str.clear_all_append(rows.lines(keep(rs)), "" <> rdoc.lines(t), '\n',
          rows_clear(rs, Eq.and.right(Str.clear(n, '\n'), rows.ok(rs), ok)),
          rlines_clear(t, Eq.and.right(rsect.ok(RSect{n, rs}), rsects.ok(t), eok))))

# LAW: parsing a ledger's lines joined by newlines gives back its tables, and
# no error, when every table reads back and there is at least one
law rsections_read:
  for +s: RSect
  for +t: List<&2, RSect>
  for +eok: {rsects.ok(s <> t) == True{} : Bool}
  {T.parse(String.join(rdoc.lines(s <> t), "\n")) == T.Toml{"", "", [], sects.of(s <> t)}
    : T.Toml}

# the text is the lines joined, which cut back into the lines
def rsections_read(s, t, eok):
  match s:
    case RSect{+n, +rs}:
      sp = Equal.sym(List<&2, String>,
        String.split(String.join(rdoc.lines(RSect{n, rs} <> t), "\n"), '\n'),
        rdoc.lines(RSect{n, rs} <> t),
        Str.split_join(TP.head.line(n),
          List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)), '\n',
          rlines_clear(RSect{n, rs} <> t, eok)))
      %sp : {T.parse.fin(T.parse.walk(_, T.Toml{"", "", [], []}))
        == T.Toml{"", "", [], sects.of(RSect{n, rs} <> t)} : T.Toml}
      walk_rdoc(RSect{n, rs} <> t, "", "", [], [], eok)

# ---------------------------------------------------------------------------
# the renderer's text as lines

# LAW: a row with no value writes nothing
law text_empty:
  for +r: Row
  for eb: {String.is_empty(row.val(r)) == True{} : Bool}
  {row.text(r) == "" : String}

def text_empty(r, eb):
  match r:
    case Q{k, +v}:
      %Equal.sym(Bool, String.is_empty(v), True{}, eb)
        : {Bool.pick(String, _, "", k ++ " = \"" ++ v ++ "\"\n") == "" : String}
      {==}
    case B{k, +v}:
      %Equal.sym(Bool, String.is_empty(v), True{}, eb)
        : {Bool.pick(String, _, "", k ++ " = " ++ v ++ "\n") == "" : String}
      {==}

# LAW: a quoted row with a value writes its line and a newline, ahead of
# whatever follows
law text_line.q:
  for +k: String
  for +v: String
  for +x: String
  for ev: {String.is_empty(v) == False{} : Bool}
  for ek: {T.bare(k) == True{} : Bool}
  {String.append(row.line(Q{k, v}), SCon{'\n', x}) == String.append(row.text(Q{k, v}), x)
    : String}

def text_line.q(k, v, x, ev, ek):
  %Equal.sym(Bool, String.is_empty(v), False{}, ev)
    : {String.append(row.line(Q{k, v}), SCon{'\n', x})
      == String.append(Bool.pick(String, _, "", k ++ " = \"" ++ v ++ "\"\n"), x) : String}
  %Equal.sym(Bool, T.bare(k), True{}, ek)
    : {String.append(String.append(Bool.pick(String, _, k, T.quote(k)), " = " ++ T.quote(v)),
        SCon{'\n', x})
      == String.append(k ++ " = \"" ++ v ++ "\"\n", x) : String}
  a1 = Equal.sym(String, String.append(String.append(k, " = " ++ T.quote(v)), SCon{'\n', x}),
    String.append(k, String.append(" = " ++ T.quote(v), SCon{'\n', x})),
    Eq.append_assoc(k, " = " ++ T.quote(v), SCon{'\n', x}))
  %a1 : {_ == String.append(k ++ " = \"" ++ v ++ "\"\n", x) : String}
  a2 = Equal.sym(String, String.append(k ++ " = \"" ++ v ++ "\"\n", x),
    String.append(k, String.append(" = \"" ++ v ++ "\"\n", x)),
    Eq.append_assoc(k, " = \"" ++ v ++ "\"\n", x))
  %a2 : {String.append(k, String.append(" = " ++ T.quote(v), SCon{'\n', x})) == _ : String}
  a3 = Equal.sym(String, String.append(String.append(v, "\""), SCon{'\n', x}),
    String.append(v, String.append("\"", SCon{'\n', x})),
    Eq.append_assoc(v, "\"", SCon{'\n', x}))
  %a3 : {String.append(k, " = \"" ++ _)
    == String.append(k, String.append(" = \"" ++ v ++ "\"\n", x)) : String}
  a4 = Equal.sym(String, String.append(String.append(v, "\"\n"), x),
    String.append(v, String.append("\"\n", x)),
    Eq.append_assoc(v, "\"\n", x))
  %a4 : {String.append(k, " = \"" ++ String.append(v, String.append("\"", SCon{'\n', x})))
    == String.append(k, " = \"" ++ _) : String}
  {==}

# LAW: a row with a value that reads back writes its line and a newline,
# ahead of whatever follows
law text_line:
  for +r: Row
  for +x: String
  for ev: {String.is_empty(row.val(r)) == False{} : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  {String.append(row.line(r), SCon{'\n', x}) == String.append(row.text(r), x) : String}

def text_line(r, x, ev, ok):
  match r:
    case Q{+k, +v}:
      text_line.q(k, v, x, ev,
        Eq.and.left(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))), ok))
    case B{+k, +v}:
      %Equal.sym(Row, B{k, v}, B{"vendor", "true"}, vendor_row(k, v, ev, ok))
        : {String.append(row.line(_), SCon{'\n', x}) == String.append(row.text(_), x) : String}
      {==}

# LAW: one row, kept or dropped, written, with whether its value is empty given
law rows_text.arm:
  for +r: Row
  for +t: List<&2, Row>
  for b: Bool
  for eb: {String.is_empty(row.val(r)) == b : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  for ih: {TP.unlines(rows.lines(keep(t))) == rows.text(t) : String}
  {TP.unlines(rows.lines(keep.put(b, r, keep(t)))) == String.append(row.text(r), rows.text(t))
    : String}

def rows_text.arm(r, t, b, eb, ok, ih):
  match b:
    case True{}:
      %Equal.sym(String, row.text(r), "", text_empty(r, eb))
        : {TP.unlines(rows.lines(keep(t))) == String.append(_, rows.text(t)) : String}
      ih
    case False{}:
      %Equal.sym(String, TP.unlines(rows.lines(keep(t))), rows.text(t), ih)
        : {String.append(row.line(r), SCon{'\n', _})
          == String.append(row.text(r), rows.text(t)) : String}
      text_line(r, rows.text(t), eb, ok)

# LAW: the lines a table's rows write, each ended by a newline, are the text
# the renderer writes for them
law rows_text:
  for +rs: List<&2, Row>
  for +eok: {rows.ok(rs) == True{} : Bool}
  {TP.unlines(rows.lines(keep(rs))) == rows.text(rs) : String}

def rows_text(rs, eok):
  match rs:
    case []:
      {==}
    case +r <> +t:
      rows_text.arm(r, t, String.is_empty(row.val(r)), {==},
        Eq.and.left(row.ok(r), rows.ok(t), eok),
        rows_text(t, Eq.and.right(row.ok(r), rows.ok(t), eok)))

# rows written ahead of a text. Proof vocabulary.
def rows.cat(rs: List<&2, Row>, x: String) -> String:
  match rs:
    case []:
      x
    case h <> t:
      String.append(row.text(h), rows.cat(t, x))

# LAW: rows written ahead of a text are their text, then it
law rows_cat:
  for +rs: List<&2, Row>
  for +x: String
  {rows.cat(rs, x) == String.append(rows.text(rs), x) : String}

def rows_cat(rs, x):
  match rs:
    case []:
      {==}
    case +r <> +t:
      %Equal.sym(String, rows.cat(t, x), String.append(rows.text(t), x), rows_cat(t, x))
        : {String.append(row.text(r), _)
          == String.append(String.append(row.text(r), rows.text(t)), x) : String}
      Equal.sym(String, String.append(String.append(row.text(r), rows.text(t)), x),
        String.append(row.text(r), String.append(rows.text(t), x)),
        Eq.append_assoc(row.text(r), rows.text(t), x))

# LAW: and two lists of rows are the first ahead of the second
law rows_cat_append:
  for +as: List<&2, Row>
  for +bs: List<&2, Row>
  for +x: String
  {rows.cat(List.append(&2, Row, as, bs), x) == rows.cat(as, rows.cat(bs, x)) : String}

def rows_cat_append(as, bs, x):
  match as:
    case []:
      {==}
    case +r <> +t:
      Equal.cong(String, String, y => String.append(row.text(r), y),
        rows.cat(List.append(&2, Row, t, bs), x), rows.cat(t, rows.cat(bs, x)),
        rows_cat_append(t, bs, x))

# LAW: a section's header and rows as the renderer writes them, a blank line
# first, ahead of whatever follows, are that blank line and the section's
# lines, when the rows' text is what the lines give
law blk_text:
  for +p: String
  for +n: String
  for +z: String
  for +u: String
  for +x: String
  for e: {String.append(u, x) == String.append(z, x) : String}
  {String.append(SCon{'\n', SCon{'[', String.append(p, String.append(n, SCon{']', SCon{'\n', z}}))}}, x)
    == SCon{'\n', String.append(String.append(SCon{'[', String.append(String.append(p, n), "]")},
      SCon{'\n', u}), x)} : String}

def blk_text(p, n, z, u, x, e):
  l1 = Eq.append_assoc(p, String.append(n, SCon{']', SCon{'\n', z}}), x)
  l2 = Equal.cong(String, String, y => String.append(p, y),
    String.append(String.append(n, SCon{']', SCon{'\n', z}}), x),
    String.append(n, SCon{']', SCon{'\n', String.append(z, x)}}),
    Eq.append_assoc(n, SCon{']', SCon{'\n', z}}, x))
  l3 = Equal.cong(String, String, y => String.append(p, String.append(n, SCon{']', SCon{'\n', y}})),
    String.append(z, x), String.append(u, x), Equal.sym(String, String.append(u, x), String.append(z, x), e))
  r1 = Eq.append_assoc(String.append(String.append(p, n), "]"), SCon{'\n', u}, x)
  r2 = Eq.append_assoc(String.append(p, n), "]", SCon{'\n', String.append(u, x)})
  r3 = Eq.append_assoc(p, n, SCon{']', SCon{'\n', String.append(u, x)}})
  Equal.cong(String, String, y => SCon{'\n', SCon{'[', y}},
    String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
    String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
    Equal.trans(String,
      String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
      String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
      String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
      Equal.trans(String,
        String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
        String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(z, x)}})),
        String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
        Equal.trans(String,
          String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
          String.append(p, String.append(String.append(n, SCon{']', SCon{'\n', z}}), x)),
          String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(z, x)}})),
          l1, l2),
        l3),
      Equal.sym(String,
        String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
        String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
        Equal.trans(String,
          String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
          String.append(String.append(String.append(p, n), "]"), SCon{'\n', String.append(u, x)}),
          String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
          r1,
          Equal.trans(String,
            String.append(String.append(String.append(p, n), "]"), SCon{'\n', String.append(u, x)}),
            String.append(String.append(p, n), SCon{']', SCon{'\n', String.append(u, x)}}),
            String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
            r2, r3)))))

# ---------------------------------------------------------------------------
# a ledger as tables of rows

# the rows of the `[package]` table
def pkg.rows(n: String, e: String, b: String, h: String) -> List<&2, Row>:
  [Q{"name", n}, Q{"entry", e}, Q{"bin", b}, Q{"hub", h}]

# the rows a source writes
def src.rows(s: M.Source) -> List<&2, Row>:
  match s:
    case M.Hub{}:
      []
    case M.Git{url, rev, tag, root, nar, vend}:
      [Q{"git", url}, Q{"rev", rev}, Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
        B{"vendor", R.vendor.word(vend)}]

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
  M.Manifest{n, e, b, h, ds, ts} = m
  RSect{"package", pkg.rows(n, e, b, h)} <> dsects(ds, tsects(ts))

# the text a ledger's tables after the first write: every table a newline
# first
def rjoin(ss: List<&2, RSect>) -> String:
  String.join.go(rdoc.lines(ss), "", "\n")

# LAW: a table's rows read back when the table does
law rsect_rows:
  for +n: String
  for +rs: List<&2, Row>
  for e: {rsect.ok(RSect{n, rs}) == True{} : Bool}
  {rows.ok(rs) == True{} : Bool}

def rsect_rows(n, rs, e):
  Eq.and.right(Str.clear(n, '\n'), rows.ok(rs),
    Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)), e))

# LAW: a source's rows are the text the renderer writes for it
law src_text:
  for +s: M.Source
  {rows.text(src.rows(s)) == R.source(s) : String}

def src_text(s):
  match s:
    case M.Hub{}:
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      Equal.cong(String, String,
        y => String.append(R.line("git", url), String.append(R.line("rev", rev),
          String.append(R.line("tag", tag), String.append(R.line("root", root),
            String.append(R.line("narHash", nar), y))))),
        String.append(R.line.bare("vendor", R.vendor.word(vend)), ""),
        R.line.bare("vendor", R.vendor.word(vend)),
        Str.append_nil(R.line.bare("vendor", R.vendor.word(vend))))

# LAW: a table, a blank line first, then the tables after it
law rjoin_cons:
  for +n: String
  for +rs: List<&2, Row>
  for +t: List<&2, RSect>
  {rjoin(RSect{n, rs} <> t)
    == SCon{'\n', String.append(TP.unlines(TP.head.line(n) <> rows.lines(keep(rs))), rjoin(t))}
    : String}

def rjoin_cons(n, rs, t):
  Equal.cong(String, String, y => SCon{'\n', y},
    String.join.go(List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)),
      TP.head.line(n), "\n"),
    String.append(TP.unlines(TP.head.line(n) <> rows.lines(keep(rs))), rjoin(t)),
    TP.join_lines(rows.lines(keep(rs)), TP.head.line(n), rdoc.lines(t)))

# LAW: a dependency as the renderer writes it, ahead of whatever follows, is a
# newline and its table's lines
law dep_text:
  for +n: String
  for +h: String
  for +e: String
  for +s: M.Source
  for +x: String
  for ok: {rows.ok(dep.rows(h, e, s)) == True{} : Bool}
  {String.append(R.dep(M.Dep{n, h, e, s}), x)
    == SCon{'\n', String.append(TP.unlines(TP.head.line("deps." ++ n)
      <> rows.lines(keep(dep.rows(h, e, s)))), x)} : String}

def dep_text(n, h, e, s, x, ok):
  +u = TP.unlines(rows.lines(keep(dep.rows(h, e, s))))
  +lh = R.line("hash", h)
  +le = R.line("entry", e)
  eu = Equal.trans(String, String.append(u, x),
    rows.cat(dep.rows(h, e, s), x),
    String.append(lh, String.append(R.source(s), String.append(le, x))),
    Equal.trans(String, String.append(u, x),
      String.append(rows.text(dep.rows(h, e, s)), x),
      rows.cat(dep.rows(h, e, s), x),
      Equal.cong(String, String, y => String.append(y, x), u, rows.text(dep.rows(h, e, s)),
        rows_text(dep.rows(h, e, s), ok)),
      Equal.sym(String, rows.cat(dep.rows(h, e, s), x),
        String.append(rows.text(dep.rows(h, e, s)), x), rows_cat(dep.rows(h, e, s), x))),
    Equal.cong(String, String, y => String.append(lh, y),
      rows.cat(List.append(&2, Row, src.rows(s), [Q{"entry", e}]), x),
      String.append(R.source(s), String.append(le, x)),
      Equal.trans(String,
        rows.cat(List.append(&2, Row, src.rows(s), [Q{"entry", e}]), x),
        rows.cat(src.rows(s), String.append(le, x)),
        String.append(R.source(s), String.append(le, x)),
        rows_cat_append(src.rows(s), [Q{"entry", e}], x),
        Equal.trans(String,
          rows.cat(src.rows(s), String.append(le, x)),
          String.append(rows.text(src.rows(s)), String.append(le, x)),
          String.append(R.source(s), String.append(le, x)),
          rows_cat(src.rows(s), String.append(le, x)),
          Equal.cong(String, String, y => String.append(y, String.append(le, x)),
            rows.text(src.rows(s)), R.source(s), src_text(s))))))
  ez = Equal.trans(String,
    String.append(String.append(lh, String.append(R.source(s), le)), x),
    String.append(lh, String.append(String.append(R.source(s), le), x)),
    String.append(lh, String.append(R.source(s), String.append(le, x))),
    Eq.append_assoc(lh, String.append(R.source(s), le), x),
    Equal.cong(String, String, y => String.append(lh, y),
      String.append(String.append(R.source(s), le), x),
      String.append(R.source(s), String.append(le, x)),
      Eq.append_assoc(R.source(s), le, x)))
  blk_text("deps.", n, String.append(lh, String.append(R.source(s), le)), u, x,
    Equal.trans(String, String.append(u, x),
      String.append(lh, String.append(R.source(s), String.append(le, x))),
      String.append(String.append(lh, String.append(R.source(s), le)), x),
      eu,
      Equal.sym(String, String.append(String.append(lh, String.append(R.source(s), le)), x),
        String.append(lh, String.append(R.source(s), String.append(le, x))), ez)))

# LAW: and so is a pinned CLI
law tool_text:
  for +n: String
  for +e: String
  for +b: String
  for +s: M.Source
  for +x: String
  for ok: {rows.ok(tool.rows(e, b, s)) == True{} : Bool}
  {String.append(R.tool(M.Tool{n, e, b, s}), x)
    == SCon{'\n', String.append(TP.unlines(TP.head.line("tools." ++ n)
      <> rows.lines(keep(tool.rows(e, b, s)))), x)} : String}

def tool_text(n, e, b, s, x, ok):
  +u = TP.unlines(rows.lines(keep(tool.rows(e, b, s))))
  +le = R.line("entry", e)
  +lb = R.line("bin", b)
  eu = Equal.trans(String, String.append(u, x),
    rows.cat(tool.rows(e, b, s), x),
    String.append(R.source(s), String.append(le, String.append(lb, x))),
    Equal.trans(String, String.append(u, x),
      String.append(rows.text(tool.rows(e, b, s)), x),
      rows.cat(tool.rows(e, b, s), x),
      Equal.cong(String, String, y => String.append(y, x), u, rows.text(tool.rows(e, b, s)),
        rows_text(tool.rows(e, b, s), ok)),
      Equal.sym(String, rows.cat(tool.rows(e, b, s), x),
        String.append(rows.text(tool.rows(e, b, s)), x), rows_cat(tool.rows(e, b, s), x))),
    Equal.trans(String,
      rows.cat(tool.rows(e, b, s), x),
      rows.cat(src.rows(s), String.append(le, String.append(lb, x))),
      String.append(R.source(s), String.append(le, String.append(lb, x))),
      rows_cat_append(src.rows(s), [Q{"entry", e}, Q{"bin", b}], x),
      Equal.trans(String,
        rows.cat(src.rows(s), String.append(le, String.append(lb, x))),
        String.append(rows.text(src.rows(s)), String.append(le, String.append(lb, x))),
        String.append(R.source(s), String.append(le, String.append(lb, x))),
        rows_cat(src.rows(s), String.append(le, String.append(lb, x))),
        Equal.cong(String, String, y => String.append(y, String.append(le, String.append(lb, x))),
          rows.text(src.rows(s)), R.source(s), src_text(s)))))
  ez = Equal.trans(String,
    String.append(String.append(R.source(s), String.append(le, lb)), x),
    String.append(R.source(s), String.append(String.append(le, lb), x)),
    String.append(R.source(s), String.append(le, String.append(lb, x))),
    Eq.append_assoc(R.source(s), String.append(le, lb), x),
    Equal.cong(String, String, y => String.append(R.source(s), y),
      String.append(String.append(le, lb), x),
      String.append(le, String.append(lb, x)),
      Eq.append_assoc(le, lb, x)))
  blk_text("tools.", n, String.append(R.source(s), String.append(le, lb)), u, x,
    Equal.trans(String, String.append(u, x),
      String.append(R.source(s), String.append(le, String.append(lb, x))),
      String.append(String.append(R.source(s), String.append(le, lb)), x),
      eu,
      Equal.sym(String, String.append(String.append(R.source(s), String.append(le, lb)), x),
        String.append(R.source(s), String.append(le, String.append(lb, x))), ez)))

# LAW: the pinned CLIs as the renderer writes them are their tables' lines,
# each table a newline first
law tools_text:
  for +ts: List<&2, M.Tool>
  for +ok: {rsects.ok(tsects(ts)) == True{} : Bool}
  {R.tools(ts) == rjoin(tsects(ts)) : String}

def tools_text(ts, ok):
  match ts:
    case []:
      {==}
    case M.Tool{+n, +e, +b, +s} <> +r:
      +ih = tools_text(r, Eq.and.right(rsect.ok(tool.sect(M.Tool{n, e, b, s})), rsects.ok(tsects(r)), ok))
      Equal.trans(String, R.tools(M.Tool{n, e, b, s} <> r),
        String.append(R.tool(M.Tool{n, e, b, s}), rjoin(tsects(r))),
        rjoin(tsects(M.Tool{n, e, b, s} <> r)),
        Equal.cong(String, String, y => String.append(R.tool(M.Tool{n, e, b, s}), y),
          R.tools(r), rjoin(tsects(r)), ih),
        Equal.trans(String,
          String.append(R.tool(M.Tool{n, e, b, s}), rjoin(tsects(r))),
          SCon{'\n', String.append(TP.unlines(TP.head.line("tools." ++ n)
            <> rows.lines(keep(tool.rows(e, b, s)))), rjoin(tsects(r)))},
          rjoin(tsects(M.Tool{n, e, b, s} <> r)),
          tool_text(n, e, b, s, rjoin(tsects(r)),
            rsect_rows("tools." ++ n, tool.rows(e, b, s),
              Eq.and.left(rsect.ok(tool.sect(M.Tool{n, e, b, s})), rsects.ok(tsects(r)), ok))),
          Equal.sym(String, rjoin(tsects(M.Tool{n, e, b, s} <> r)),
            SCon{'\n', String.append(TP.unlines(TP.head.line("tools." ++ n)
              <> rows.lines(keep(tool.rows(e, b, s)))), rjoin(tsects(r)))},
            rjoin_cons("tools." ++ n, tool.rows(e, b, s), tsects(r)))))

# LAW: and the dependencies, then the pinned CLIs
law deps_text:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +ok: {rsects.ok(dsects(ds, tsects(ts))) == True{} : Bool}
  {String.append(R.deps(ds), R.tools(ts)) == rjoin(dsects(ds, tsects(ts))) : String}

def deps_text(ds, ts, ok):
  match ds:
    case []:
      tools_text(ts, ok)
    case M.Dep{+n, +h, +e, +s} <> +t:
      +rest = dsects(t, tsects(ts))
      +ih = deps_text(t, ts, Eq.and.right(rsect.ok(dep.sect(M.Dep{n, h, e, s})), rsects.ok(rest), ok))
      Equal.trans(String,
        String.append(String.append(R.dep(M.Dep{n, h, e, s}), R.deps(t)), R.tools(ts)),
        String.append(R.dep(M.Dep{n, h, e, s}), rjoin(rest)),
        rjoin(dsects(M.Dep{n, h, e, s} <> t, tsects(ts))),
        Equal.trans(String,
          String.append(String.append(R.dep(M.Dep{n, h, e, s}), R.deps(t)), R.tools(ts)),
          String.append(R.dep(M.Dep{n, h, e, s}), String.append(R.deps(t), R.tools(ts))),
          String.append(R.dep(M.Dep{n, h, e, s}), rjoin(rest)),
          Eq.append_assoc(R.dep(M.Dep{n, h, e, s}), R.deps(t), R.tools(ts)),
          Equal.cong(String, String, y => String.append(R.dep(M.Dep{n, h, e, s}), y),
            String.append(R.deps(t), R.tools(ts)), rjoin(rest), ih)),
        Equal.trans(String,
          String.append(R.dep(M.Dep{n, h, e, s}), rjoin(rest)),
          SCon{'\n', String.append(TP.unlines(TP.head.line("deps." ++ n)
            <> rows.lines(keep(dep.rows(h, e, s)))), rjoin(rest))},
          rjoin(dsects(M.Dep{n, h, e, s} <> t, tsects(ts))),
          dep_text(n, h, e, s, rjoin(rest),
            rsect_rows("deps." ++ n, dep.rows(h, e, s),
              Eq.and.left(rsect.ok(dep.sect(M.Dep{n, h, e, s})), rsects.ok(rest), ok))),
          Equal.sym(String, rjoin(dsects(M.Dep{n, h, e, s} <> t, tsects(ts))),
            SCon{'\n', String.append(TP.unlines(TP.head.line("deps." ++ n)
              <> rows.lines(keep(dep.rows(h, e, s)))), rjoin(rest))},
            rjoin_cons("deps." ++ n, dep.rows(h, e, s), rest))))

# LAW: a ledger as the renderer writes it is its tables' lines joined by
# newlines
law show_text:
  for +m: M.Manifest
  for +ok: {rsects.ok(lsects(m)) == True{} : Bool}
  {R.show(m) == String.join(rdoc.lines(lsects(m)), "\n") : String}

def show_text(m, ok):
  match m:
    case M.Manifest{+n, +e, +b, +h, +ds, +ts}:
      +d = dsects(ds, tsects(ts))
      +p = pkg.rows(n, e, b, h)
      +pk = {RSect{"package", p} : RSect}
      +dt = deps_text(ds, ts, Eq.and.right(rsect.ok(pk), rsects.ok(d), ok))
      +pt = rows_text(p, rsect_rows("package", p, Eq.and.left(rsect.ok(pk), rsects.ok(d), ok)))
      Equal.trans(String, R.show(M.Manifest{n, e, b, h, ds, ts}),
        "[package]\n" ++ rows.cat(p, rjoin(d)),
        String.join(rdoc.lines(pk <> d), "\n"),
        Equal.cong(String, String,
          y => "[package]\n" ++ String.append(R.line("name", n), String.append(R.line("entry", e),
            String.append(R.line("bin", b), String.append(R.line("hub", h), y)))),
          String.append(R.deps(ds), R.tools(ts)), rjoin(d), dt),
        Equal.trans(String, "[package]\n" ++ rows.cat(p, rjoin(d)),
          "[package]\n" ++ String.append(TP.unlines(rows.lines(keep(p))), rjoin(d)),
          String.join(rdoc.lines(pk <> d), "\n"),
          Equal.cong(String, String, y => "[package]\n" ++ y,
            rows.cat(p, rjoin(d)), String.append(TP.unlines(rows.lines(keep(p))), rjoin(d)),
            Equal.trans(String, rows.cat(p, rjoin(d)), String.append(rows.text(p), rjoin(d)),
              String.append(TP.unlines(rows.lines(keep(p))), rjoin(d)),
              rows_cat(p, rjoin(d)),
              Equal.cong(String, String, y => String.append(y, rjoin(d)),
                rows.text(p), TP.unlines(rows.lines(keep(p))),
                Equal.sym(String, TP.unlines(rows.lines(keep(p))), rows.text(p), pt)))),
          Equal.sym(String, String.join(rdoc.lines(pk <> d), "\n"),
            String.append(TP.unlines("[package]" <> rows.lines(keep(p))), rjoin(d)),
            TP.join_lines(rows.lines(keep(p)), "[package]", rdoc.lines(d)))))

# ---------------------------------------------------------------------------
# a renderable ledger's tables read back

# LAW: the renderer's check for a char is the proofs' one
law clear_same:
  for +s: String
  for +c: Char
  {R.clear(s, c) == Str.clear(s, c) : Bool}

def clear_same(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bool, Bool, y => Bool.and(Bool.not(Char.is_eq(h, c)), y),
        R.clear(t, c), Str.clear(t, c), clear_same(t, c))

# LAW: a clean value holds no newline
law clean_nl:
  for +s: String
  for +e: {R.clean(s) == True{} : Bool}
  {Str.clear(s, '\n') == True{} : Bool}

def clean_nl(s, e):
  Equal.trans(Bool, Str.clear(s, '\n'), R.clear(s, '\n'), True{},
    Equal.sym(Bool, R.clear(s, '\n'), Str.clear(s, '\n'), clear_same(s, '\n')),
    Eq.and.right(R.clear(s, '\\'), R.clear(s, '\n'),
      Eq.and.right(R.clear(s, '"'), Bool.and(R.clear(s, '\\'), R.clear(s, '\n')), e)))

# LAW: the vendor row reads back whichever bit it carries
law vend_ok:
  for vend: Bool
  {row.ok(B{"vendor", R.vendor.word(vend)}) == True{} : Bool}

def vend_ok(vend):
  match vend:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a clean source's rows, ahead of rows that read back, read back
law src_rows_ok:
  for +s: M.Source
  for +rest: List<&2, Row>
  for es: {R.source.ok(s) == True{} : Bool}
  for er: {rows.ok(rest) == True{} : Bool}
  {rows.ok(List.append(&2, Row, src.rows(s), rest)) == True{} : Bool}

def src_rows_ok(s, rest, es, er):
  match s:
    case M.Hub{}:
      er
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +cs = Eq.and.right(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
      +c1 = Eq.and.left(Bool.and(R.clean(url), R.clean(rev)),
        Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar))), cs)
      +c2 = Eq.and.right(Bool.and(R.clean(url), R.clean(rev)),
        Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar))), cs)
      +c3 = Eq.and.right(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)), c2)
      Str.and_true(Str.clear(url, '\n'), rows.ok(List.append(&2, Row,
          [Q{"rev", rev}, Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
            B{"vendor", R.vendor.word(vend)}], rest)),
        clean_nl(url, Eq.and.left(R.clean(url), R.clean(rev), c1)),
        Str.and_true(Str.clear(rev, '\n'), rows.ok(List.append(&2, Row,
            [Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
              B{"vendor", R.vendor.word(vend)}], rest)),
          clean_nl(rev, Eq.and.right(R.clean(url), R.clean(rev), c1)),
          Str.and_true(Str.clear(tag, '\n'), rows.ok(List.append(&2, Row,
              [Q{"root", root}, Q{"narHash", nar}, B{"vendor", R.vendor.word(vend)}], rest)),
            clean_nl(tag, Eq.and.left(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)), c2)),
            Str.and_true(Str.clear(root, '\n'), rows.ok(List.append(&2, Row,
                [Q{"narHash", nar}, B{"vendor", R.vendor.word(vend)}], rest)),
              clean_nl(root, Eq.and.left(R.clean(root), R.clean(nar), c3)),
              Str.and_true(Str.clear(nar, '\n'), rows.ok(List.append(&2, Row,
                  [B{"vendor", R.vendor.word(vend)}], rest)),
                clean_nl(nar, Eq.and.right(R.clean(root), R.clean(nar), c3)),
                Str.and_true(row.ok(B{"vendor", R.vendor.word(vend)}), rows.ok(rest),
                  vend_ok(vend), er))))))

# LAW: a dependency that can be written has a table that reads back
law dep_sect_ok:
  for +d: M.Dep
  for +e: {R.dep.ok(d) == True{} : Bool}
  {rsect.ok(dep.sect(d)) == True{} : Bool}

def dep_sect_ok(d, e):
  match d:
    case M.Dep{+n, +h, +en, +s}:
      +l = Eq.and.left(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
        Bool.and(R.clean(en), R.source.ok(s)), e)
      +r = Eq.and.right(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
        Bool.and(R.clean(en), R.source.ok(s)), e)
      Str.and_true(Str.clear(n, '\n'), rows.ok(dep.rows(h, en, s)),
        clean_nl(n, Eq.and.left(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h)), l)),
        Str.and_true(Str.clear(h, '\n'),
          rows.ok(List.append(&2, Row, src.rows(s), [Q{"entry", en}])),
          clean_nl(h, Eq.and.right(Bool.not(String.is_empty(h)), R.clean(h),
            Eq.and.right(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h)), l))),
          src_rows_ok(s, [Q{"entry", en}], Eq.and.right(R.clean(en), R.source.ok(s), r),
            Str.and_true(Str.clear(en, '\n'), True{},
              clean_nl(en, Eq.and.left(R.clean(en), R.source.ok(s), r)), {==}))))

# LAW: and so does a pinned CLI that can be written
law tool_sect_ok:
  for +pin: M.Tool
  for +e: {R.tool.ok(pin) == True{} : Bool}
  {rsect.ok(tool.sect(pin)) == True{} : Bool}

def tool_sect_ok(pin, e):
  match pin:
    case M.Tool{+n, +en, +b, +s}:
      +r = Eq.and.right(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)), R.source.ok(s)), e)
      +eb = Eq.and.left(Bool.and(R.clean(en), R.clean(b)), R.source.ok(s), r)
      Str.and_true(Str.clear(n, '\n'), rows.ok(tool.rows(en, b, s)),
        clean_nl(n, Eq.and.left(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)),
          R.source.ok(s)), e)),
        src_rows_ok(s, [Q{"entry", en}, Q{"bin", b}],
          Eq.and.right(Bool.and(R.clean(en), R.clean(b)), R.source.ok(s), r),
          Str.and_true(Str.clear(en, '\n'), rows.ok([Q{"bin", b}]),
            clean_nl(en, Eq.and.left(R.clean(en), R.clean(b), eb)),
            Str.and_true(Str.clear(b, '\n'), True{},
              clean_nl(b, Eq.and.right(R.clean(en), R.clean(b), eb)), {==}))))

# LAW: the tables of pinned CLIs that can be written read back
law tsects_ok:
  for +ts: List<&2, M.Tool>
  for +e: {R.tools.ok(ts) == True{} : Bool}
  {rsects.ok(tsects(ts)) == True{} : Bool}

def tsects_ok(ts, e):
  match ts:
    case []:
      {==}
    case +h <> +t:
      Str.and_true(rsect.ok(tool.sect(h)), rsects.ok(tsects(t)),
        tool_sect_ok(h, Eq.and.left(R.tool.ok(h), R.tools.ok(t), e)),
        tsects_ok(t, Eq.and.right(R.tool.ok(h), R.tools.ok(t), e)))

# LAW: and the dependencies' tables, ahead of tables that read back
law dsects_ok:
  for +ds: List<&2, M.Dep>
  for +rest: List<&2, RSect>
  for +e: {R.deps.ok(ds) == True{} : Bool}
  for er: {rsects.ok(rest) == True{} : Bool}
  {rsects.ok(dsects(ds, rest)) == True{} : Bool}

def dsects_ok(ds, rest, e, er):
  match ds:
    case []:
      er
    case +h <> +t:
      Str.and_true(rsect.ok(dep.sect(h)), rsects.ok(dsects(t, rest)),
        dep_sect_ok(h, Eq.and.left(R.dep.ok(h), R.deps.ok(t), e)),
        dsects_ok(t, rest, Eq.and.right(R.dep.ok(h), R.deps.ok(t), e), er))

# LAW: a renderable ledger's tables read back
law lsects_ok:
  for +m: M.Manifest
  for +e: {R.renderable(m) == True{} : Bool}
  {rsects.ok(lsects(m)) == True{} : Bool}

def lsects_ok(m, e):
  match m:
    case M.Manifest{+n, +en, +b, +h, +ds, +ts}:
      +l = Eq.and.left(Bool.and(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h))),
        Bool.and(R.deps.ok(ds), R.tools.ok(ts)), e)
      +r = Eq.and.right(Bool.and(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h))),
        Bool.and(R.deps.ok(ds), R.tools.ok(ts)), e)
      +l1 = Eq.and.left(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h)), l)
      +l2 = Eq.and.right(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h)), l)
      Str.and_true(rsect.ok(RSect{"package", pkg.rows(n, en, b, h)}),
        rsects.ok(dsects(ds, tsects(ts))),
        Str.and_true(Str.clear(n, '\n'), rows.ok([Q{"entry", en}, Q{"bin", b}, Q{"hub", h}]),
          clean_nl(n, Eq.and.left(R.clean(n), R.clean(en), l1)),
          Str.and_true(Str.clear(en, '\n'), rows.ok([Q{"bin", b}, Q{"hub", h}]),
            clean_nl(en, Eq.and.right(R.clean(n), R.clean(en), l1)),
            Str.and_true(Str.clear(b, '\n'), rows.ok([Q{"hub", h}]),
              clean_nl(b, Eq.and.left(R.clean(b), R.clean(h), l2)),
              Str.and_true(Str.clear(h, '\n'), True{},
                clean_nl(h, Eq.and.right(R.clean(b), R.clean(h), l2)), {==})))),
        dsects_ok(ds, tsects(ts), Eq.and.left(R.deps.ok(ds), R.tools.ok(ts), r),
          tsects_ok(ts, Eq.and.right(R.deps.ok(ds), R.tools.ok(ts), r))))

# LAW: a renderable ledger's text, parsed, is its tables, with no error
law ledger_sections_read:
  for +m: M.Manifest
  for +e: {R.renderable(m) == True{} : Bool}
  {T.parse(R.show(m)) == T.Toml{"", "", [], sects.of(lsects(m))} : T.Toml}

def ledger_sections_read(m, e):
  match m:
    case M.Manifest{+n, +en, +b, +h, +ds, +ts}:
      +ok = lsects_ok(M.Manifest{n, en, b, h, ds, ts}, e)
      %Equal.sym(String, R.show(M.Manifest{n, en, b, h, ds, ts}),
        String.join(rdoc.lines(lsects(M.Manifest{n, en, b, h, ds, ts})), "\n"),
        show_text(M.Manifest{n, en, b, h, ds, ts}, ok))
        : {T.parse(_) == T.Toml{"", "", [], sects.of(lsects(M.Manifest{n, en, b, h, ds, ts}))}
          : T.Toml}
      rsections_read(RSect{"package", pkg.rows(n, en, b, h)}, dsects(ds, tsects(ts)), ok)

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

# LAW: a row's pair answers a lookup with its value when the key is its own
law value_at_row:
  for +r: Row
  for rest: String
  for +k: String
  {T.value.at(row.kv(r), rest, k) == Bool.pick(String, String.eq(row.key(r), k), row.val(r), rest)
    : String}

def value_at_row(r, rest, k):
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
  {M.flag(R.vendor.word(vend)) == vend : Bool}

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
  {M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, M.flag(R.vendor.word(vend)))
    == M.Git{url, rev, tag, root, nar, vend} : M.Source}

def git_source(url, rev, tag, root, nar, vend, eu, er):
  %Equal.sym(Bool, String.is_empty(url), False{}, eu)
    : {M.source.go(_, url, rev, tag, M.root.or(root), nar, M.flag(R.vendor.word(vend)))
      == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  %Equal.sym(Bool, String.is_empty(root), False{}, er)
    : {M.source.go(False{}, url, rev, tag, Bool.pick(String, _, ".", root), nar,
        M.flag(R.vendor.word(vend))) == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  %Equal.sym(Bool, M.flag(R.vendor.word(vend)), vend, flag_word(vend))
    : {M.source.go(False{}, url, rev, tag, root, nar, _)
      == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  {==}

# LAW: a clean source is read from its rows, whatever follows them, as itself
law src_reads:
  for +s: M.Source
  for +rest: List<&2, Row>
  for es: {R.source.ok(s) == True{} : Bool}
  for er: {M.source_of(rows.kvs(List.append(&2, Row, src.rows(s), rest))) == M.source_of(rows.kvs(src.rows(s)))
    : M.Source}
  {M.source_of(rows.kvs(List.append(&2, Row, src.rows(s), rest))) == s : M.Source}

def src_reads(s, rest, es, er):
  match s:
    case M.Hub{}:
      er
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
      Equal.trans(M.Source,
        M.source_of(rows.kvs(List.append(&2, Row, src.rows(M.Git{url, rev, tag, root, nar, vend}), rest))),
        M.source_of(rows.kvs(src.rows(M.Git{url, rev, tag, root, nar, vend}))),
        M.Git{url, rev, tag, root, nar, vend},
        er,
        git_source(url, rev, tag, root, nar, vend,
          Eq.not.true(String.is_empty(url),
            Eq.and.left(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)),
          Eq.not.true(String.is_empty(root),
            Eq.and.right(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne))))

# LAW: dropping nothing off a string keeps it
law drop_zero:
  for +s: String
  {String.drop(s, 0n) == s : String}

def drop_zero(s):
  match s:
    case SNil{}:
      {==}
    case SCon{_c, _t}:
      {==}

# LAW: a dependency's table, as it reads back, is read as the dependency
law dep_read:
  for +n: String
  for +h: String
  for +en: String
  for +s: M.Source
  for ok: {R.dep.ok(M.Dep{n, h, en, s}) == True{} : Bool}
  {M.dep_of("deps." ++ n, rows.kvs(keep(dep.rows(h, en, s)))) == M.Dep{n, h, en, s} : M.Dep}

def dep_read(n, h, en, s, ok):
  match s:
    case M.Hub{}:
      +rs = dep.rows(h, en, M.Hub{})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"), M.source_of(rows.kvs(keep(rs)))}
          == M.Dep{n, h, en, M.Hub{}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _, M.source_of(rows.kvs(keep(rs)))} == M.Dep{n, h, en, M.Hub{}} : M.Dep}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Hub{},
        src_keep(rs, M.Hub{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))
        : {M.Dep{String.drop(n, 0n), h, en, _} == M.Dep{n, h, en, M.Hub{}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Dep{_, h, en, M.Hub{}} == M.Dep{n, h, en, M.Hub{}} : M.Dep}
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = dep.rows(h, en, M.Git{url, rev, tag, root, nar, vend})
      +es = Eq.and.right(R.clean(en), R.source.ok(M.Git{url, rev, tag, root, nar, vend}),
        Eq.and.right(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
          Bool.and(R.clean(en), R.source.ok(M.Git{url, rev, tag, root, nar, vend})), ok))
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"), M.source_of(rows.kvs(keep(rs)))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _, M.source_of(rows.kvs(keep(rs)))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Git{url, rev, tag, root, nar, vend},
        src_keep(rs, M.Git{url, rev, tag, root, nar, vend}, {==}, {==}, {==}, {==}, {==}, {==},
          git_source(url, rev, tag, root, nar, vend,
            Eq.not.true(String.is_empty(url),
              Eq.and.left(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)),
            Eq.not.true(String.is_empty(root),
              Eq.and.right(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)))))
        : {M.Dep{String.drop(n, 0n), h, en, _} == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Dep{_, h, en, M.Git{url, rev, tag, root, nar, vend}} == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      {==}

# LAW: a pinned CLI's table, as it reads back, is read as the pin
law tool_read:
  for +n: String
  for +en: String
  for +b: String
  for +s: M.Source
  for ok: {R.tool.ok(M.Tool{n, en, b, s}) == True{} : Bool}
  {M.tool_of("tools." ++ n, rows.kvs(keep(tool.rows(en, b, s)))) == M.Tool{n, en, b, s} : M.Tool}

def tool_read(n, en, b, s, ok):
  match s:
    case M.Hub{}:
      +rs = tool.rows(en, b, M.Hub{})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Tool{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "bin"), M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Hub{}} : M.Tool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "bin"), M.value(rows.kvs(rs), "bin"),
        value_keep(rs, "bin", {==}))
        : {M.Tool{String.drop(n, 0n), en, _, M.source_of(rows.kvs(keep(rs)))} == M.Tool{n, en, b, M.Hub{}} : M.Tool}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Hub{},
        src_keep(rs, M.Hub{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))
        : {M.Tool{String.drop(n, 0n), en, b, _} == M.Tool{n, en, b, M.Hub{}} : M.Tool}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Tool{_, en, b, M.Hub{}} == M.Tool{n, en, b, M.Hub{}} : M.Tool}
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = tool.rows(en, b, M.Git{url, rev, tag, root, nar, vend})
      +es = Eq.and.right(Bool.and(R.clean(en), R.clean(b)),
        R.source.ok(M.Git{url, rev, tag, root, nar, vend}),
        Eq.and.right(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)),
          R.source.ok(M.Git{url, rev, tag, root, nar, vend})), ok))
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
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
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Tool{_, en, b, M.Git{url, rev, tag, root, nar, vend}} == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      {==}

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
  for +e: {R.deps.ok(ds) == True{} : Bool}
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
        dep_read(n, h, en, s, Eq.and.left(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e)))
        : {_ <> M.deps(sects.of(rest)) == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      %Equal.sym(List<&2, M.Dep>, M.deps(sects.of(rest)), t,
        deps_read(t, ts, Eq.and.right(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e)))
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
  for +e: {R.tools.ok(ts) == True{} : Bool}
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
        tool_read(n, en, b, s, Eq.and.left(R.tool.ok(M.Tool{n, en, b, s}), R.tools.ok(t), e)))
        : {_ <> M.tools(sects.of(tsects(t))) == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      %Equal.sym(List<&2, M.Tool>, M.tools(sects.of(tsects(t))), t,
        tsects_read(t, Eq.and.right(R.tool.ok(M.Tool{n, en, b, s}), R.tools.ok(t), e)))
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

# LAW: a dependency's rows name its hash once, whatever its source
law once_hash:
  for +h: String
  for +en: String
  for +s: M.Source
  {rows.once(dep.rows(h, en, s), "hash") == True{} : Bool}

def once_hash(h, en, s):
  match s:
    case M.Hub{}:
      {==}
    case M.Git{_u, _r, _t, _o, _n, _v}:
      {==}

# LAW: the tables of dependencies that have hashes, ahead of the pins', miss
# no hash
law missing_read:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +e: {R.deps.ok(ds) == True{} : Bool}
  {M.missing(sects.of(dsects(ds, tsects(ts)))) == "" : String}

def missing_read(ds, ts, e):
  match ds:
    case []:
      tmissing(ts)
    case M.Dep{+n, +h, +en, +s} <> +t:
      +rs = dep.rows(h, en, s)
      +rest = dsects(t, tsects(ts))
      +l = Eq.and.left(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
        Bool.and(R.clean(en), R.source.ok(s)),
        Eq.and.left(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e))
      +eh = Eq.not.true(String.is_empty(h),
        Eq.and.left(Bool.not(String.is_empty(h)), R.clean(h),
          Eq.and.right(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h)), l)))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.missing.at(Bool.and(_, String.is_empty(M.value(rows.kvs(keep(rs)), "hash"))),
          "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", once_hash(h, en, s)))
        : {M.missing.at(String.is_empty(_), "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      %Equal.sym(Bool, String.is_empty(h), False{}, eh)
        : {M.missing.at(_, "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      missing_read(t, ts, Eq.and.right(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e))

# LAW: a renderable ledger's tables are read as the ledger
law read_ledger:
  for +n: String
  for +en: String
  for +b: String
  for +h: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +edk: {R.deps.ok(ds) == True{} : Bool}
  for +etk: {R.tools.ok(ts) == True{} : Bool}
  {M.read("", sects.of(lsects(M.Manifest{n, en, b, h, ds, ts})))
    == M.Good{M.Manifest{n, en, b, h, ds, ts}} : M.Read}

def read_ledger(n, en, b, h, ds, ts, edk, etk):
  +p = pkg.rows(n, en, b, h)
  +d = dsects(ds, tsects(ts))
  +s = sects.of(lsects(M.Manifest{n, en, b, h, ds, ts}))
  +g = {M.Good{M.Manifest{n, en, b, h, ds, ts}} : M.Read}
  %Equal.sym(String, M.missing(sects.of(d)), "", missing_read(ds, ts, edk))
    : {M.read.go(String.is_empty(M.problem("", _)), M.problem("", _), s) == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "name"), M.value(rows.kvs(p), "name"),
    value_keep(p, "name", {==}))
    : {M.Good{M.Manifest{_, M.value(rows.kvs(keep(p)), "entry"), M.value(rows.kvs(keep(p)), "bin"),
        M.value(rows.kvs(keep(p)), "hub"), M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "entry"), M.value(rows.kvs(p), "entry"),
    value_keep(p, "entry", {==}))
    : {M.Good{M.Manifest{n, _, M.value(rows.kvs(keep(p)), "bin"),
        M.value(rows.kvs(keep(p)), "hub"), M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "bin"), M.value(rows.kvs(p), "bin"),
    value_keep(p, "bin", {==}))
    : {M.Good{M.Manifest{n, en, _, M.value(rows.kvs(keep(p)), "hub"), M.deps(sects.of(d)),
        M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "hub"), M.value(rows.kvs(p), "hub"),
    value_keep(p, "hub", {==}))
    : {M.Good{M.Manifest{n, en, b, _, M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(List<&2, M.Dep>, M.deps(sects.of(d)), ds, deps_read(ds, ts, edk))
    : {M.Good{M.Manifest{n, en, b, h, _, M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(List<&2, M.Tool>, M.tools(sects.of(d)), ts,
    Equal.trans(List<&2, M.Tool>, M.tools(sects.of(d)), M.tools(sects.of(tsects(ts))), ts,
      dtools_skip(ds, tsects(ts)), tsects_read(ts, etk)))
    : {M.Good{M.Manifest{n, en, b, h, ds, _}} == g : M.Read}
  {==}

# LAW: a ledger ez can render, rendered, parses back to the model it was
# rendered from
law ledger_reads_back:
  for +m: M.Manifest
  for +e: {R.renderable(m) == True{} : Bool}
  {M.parse(R.show(m)) == M.Good{m} : M.Read}

def ledger_reads_back(m, e):
  match m:
    case M.Manifest{+n, +en, +b, +h, +ds, +ts}:
      +p = pkg.rows(n, en, b, h)
      +d = dsects(ds, tsects(ts))
      +s = sects.of(lsects(M.Manifest{n, en, b, h, ds, ts}))
      +r = Eq.and.right(Bool.and(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h))),
        Bool.and(R.deps.ok(ds), R.tools.ok(ts)), e)
      +edk = Eq.and.left(R.deps.ok(ds), R.tools.ok(ts), r)
      +etk = Eq.and.right(R.deps.ok(ds), R.tools.ok(ts), r)
      Equal.trans(M.Read, M.parse(R.show(M.Manifest{n, en, b, h, ds, ts})),
        M.read("", s), M.Good{M.Manifest{n, en, b, h, ds, ts}},
        Equal.cong(T.Toml, M.Read, t => M.parse.go(t),
          T.parse(R.show(M.Manifest{n, en, b, h, ds, ts})), T.Toml{"", "", [], s},
          ledger_sections_read(M.Manifest{n, en, b, h, ds, ts}, e)),
        read_ledger(n, en, b, h, ds, ts, edk, etk))
