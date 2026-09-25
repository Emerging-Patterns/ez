# toml/toml: ez's view of a TOML document: sections of string pairs. ez's
# ledger and lock are documents of tables of string (and one boolean) pairs,
# and every command reads them as a list of sections, each a header's
# segments and the pairs under it. Reading and writing TOML are eztoml's:
# `parse` walks the document eztoml's `parse` reads into that list, and
# `normal` writes a document through eztoml's `render`. Only eztoml's
# interface, `main.bend`, is imported; that a document it renders reads back
# as itself is its TOML-RT-1, trusted as EZ-TRUST-8.
#
# The rest is ez's own and pure: finding a key's value, a header's segments,
# and the text of a section in the form ez assembles a document in before
# eztoml writes it (`render`). That form is the TOML ez wrote before eztoml
# 0.4, so an old ledger or lock and a new one read to the same sections.
import Base
import 0xb652b3fca73c8a28ae49abaa395bb530/main.bend as E

# a key and the string written for it
type Kv is Data:
  Kv{key: String, val: String}

# a section header and the pairs under it, in the order they were written
type Sect is Data:
  Sect{name: String, pairs: List<&2, Kv>}

# a document read: the first error, "" when there is none, a name kept for
# the shape callers match on (always ""), the pairs above the first header,
# and every section that holds a pair, or holds no table, in document order
type Toml is Data:
  Toml{bad: String, name: String, pairs: List<&2, Kv>, done: List<&2, Sect>}

# this pair's value when the key matches, otherwise whatever the rest of the
# table gave
def value.at(kv: Kv, rest: String, key: String) -> String:
  Kv{kk, vv} = kv
  Bool.pick(String, String.eq(kk, key), vv, rest)

# the value written for a key in a table, or "" when it is absent. The scan
# recurses first and picks after, so no recursive call hides inside a branch.
def value(pairs: List<&2, Kv>, +key: String) -> String:
  match pairs:
    case []:
      ""
    case hd <> tl:
      value.at(hd, value(tl, key), key)

# the sections a parse found, in the order they were written
def sects(doc: Toml) -> List<&2, Sect>:
  Toml{_bad, _name, _pairs, done} = doc
  done

# ---------------------------------------------------------------------------
# a header's segments

# what a header's next character is: the quoting toggles, an unquoted dot cuts,
# anything else is kept
type Sym is Data:
  SQuote{}
  SDot{}
  SKeep{ch: Char}

# a header char classified. `+ch` because it is both asked about and kept.
def seg.sym(+ch: Char) -> Sym:
  Bool.pick(Sym, Char.is_eq(ch, '"'), SQuote{},
    Bool.pick(Sym, Char.is_eq(ch, '.'), SDot{}, SKeep{ch}))

# a header being cut apart: `quoted` is true inside quotes, `cur` is the segment
# being gathered and `out` the finished ones, both reversed
type Split is Data:
  Split{quoted: Bool, cur: List<&2, Char>, out: List<&2, String>}

# the segment gathered so far, in order
def seg.done(cur: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, cur))

# a dot inside quotes is part of the segment; outside, it ends one
def seg.dot(quoted: Bool, cur: List<&2, Char>, out: List<&2, String>) -> Split:
  match quoted:
    case True{}:
      Split{True{}, '.' <> cur, out}
    case False{}:
      Split{False{}, [], seg.done(cur) <> out}

# the state once a char has been classified
def seg.go(st: Split, sym: Sym) -> Split:
  Split{quoted, cur, out} = st
  match sym:
    case SQuote{}:
      Split{Bool.not(quoted), cur, out}
    case SDot{}:
      seg.dot(quoted, cur, out)
    case SKeep{ch}:
      Split{quoted, ch <> cur, out}

# one char of a header against the state
def seg.step(st: Split, ch: Char) -> Split:
  seg.go(st, seg.sym(ch))

# the segment still being gathered, closed, and the rest put back in order
def seg.fin(st: Split) -> List<&2, String>:
  Split{_quoted, cur, out} = st
  List.reverse(&2, String, seg.done(cur) <> out)

# the walk one char at a time, written out rather than folded
def seg.walk(cs: List<&2, Char>, st: Split) -> Split:
  match cs:
    case []:
      st
    case hd <> tl:
      seg.walk(tl, seg.step(st, hd))

# a header's segments, unquoted. `packages."0x0a".files` is three of them, and a
# quoted segment may hold the dots a bare one may not.
def segments(head: String) -> List<&2, String>:
  seg.fin(seg.walk(String.to_list(head), Split{False{}, [], []}))

# a string in quotes, which is how a segment or a key that is not bare is
# written, and how every value is
def quote(+text: String) -> String:
  "\"" ++ text ++ "\""

# a char a bare key may hold. `+ch` because it is asked four questions; a
# predicate handed to a fold may not take one, so it is split out here.
def bare.at(+ch: Char) -> Bool:
  Bool.or(Char.is_alpha(ch), Bool.or(Char.is_digit(ch),
    Bool.or(Char.is_eq(ch, '_'), Char.is_eq(ch, '-'))))

# one step of the walk, with the head's answer in hand. `Bool.and` runs both
# of its sides, so the first char that a bare key may not hold still cost a
# walk of the rest of the key.
def bare.all.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether every char of a key is one a bare key may hold. Base's `List.all`
# applies an erased function parameter and so falls outside the termination
# check; this walk is structural.
def bare.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hd <> tl:
      bare.all.step(bare.at(hd), _u => bare.all(tl))

# whether a key can be written without quotes
def bare(+text: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(text)), bare.all(String.to_list(text)))

# a key as it is written: bare when it can be, quoted when it must be
def key(+text: String) -> String:
  Bool.pick(String, bare(text), text, quote(text))

# ---------------------------------------------------------------------------
# a document as ez assembles it

# one `key = "value"` line
def render.pair(kv: Kv) -> String:
  Kv{kk, vv} = kv
  key(kk) ++ " = " ++ quote(vv) ++ "\n"

# every pair of a section, in the order it holds them
def render.pairs(ps: List<&2, Kv>) -> String:
  match ps:
    case []:
      ""
    case hd <> tl:
      render.pair(hd) ++ render.pairs(tl)

# one table: its header, then its pairs. The header is written as it is given,
# so a caller that needs a quoted segment quotes it.
def render.sect(sect: Sect) -> String:
  Sect{nn, ps} = sect
  "[" ++ nn ++ "]\n" ++ render.pairs(ps)

# every table of a document
def render.all(ss: List<&2, Sect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case hd <> tl:
      render.sect(hd) <> render.all(tl)

# a document of tables, one blank line between them, as ez assembles it;
# `normal` is what is written
def render(ss: List<&2, Sect>) -> String:
  String.join(render.all(ss), "\n")

# a document written as eztoml writes it: read by eztoml, and rendered back
def normal(text: String) -> String:
  E.render(E.parse(text))

# ---------------------------------------------------------------------------
# a document read

# a truth value as TOML writes it
def flag.text(bit: Bool) -> String:
  match bit:
    case True{}:
      "true"
    case False{}:
      "false"

# a pair whose value is written as text: a string or a boolean, as ez writes
# them; an integer as its digits. A table, an array or an inline table is not
# a pair of the section.
def pair.of(+name: String, val: E.Val) -> List<&2, Kv>:
  match val:
    case E.VStr{text}:
      [Kv{name, text}]
    case E.VSpan{src, nn}:
      [Kv{name, E.string(E.VSpan{src, nn})}]
    case E.VBool{bit}:
      [Kv{name, flag.text(bit)}]
    case E.VInt{_sign, digits}:
      [Kv{name, digits}]
    case _:
      []

# the pairs among a table's rows, in order
def pairs.of(rows: List<&2, E.Val>) -> List<&2, Kv>:
  match rows:
    case []:
      []
    case E.VPair{name, val} <> tl:
      List.append(&2, Kv, pair.of(name, val), pairs.of(tl))
    case _hd <> tl:
      pairs.of(tl)

# whether a row is a table
def row.table(row: E.Val) -> Bool:
  match row:
    case E.VPair{_name, E.VHead{_path, _rows}}:
      True{}
    case _:
      False{}

# the rest of the walk, when this row was not a table
def has.table.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a table's rows hold a table, stopping at the first
def has.table(rows: List<&2, E.Val>) -> Bool:
  match rows:
    case []:
      False{}
    case hd <> tl:
      has.table.step(row.table(hd), _u => has.table(tl))

# a header as ez names it: its segments, each bare or quoted, joined by dots
def head.of(segs: List<&2, String>) -> String:
  match segs:
    case []:
      ""
    case +hd <> []:
      key(hd)
    case +hd <> tl:
      key(hd) ++ "." ++ head.of(tl)

# a table's section, when it holds a pair or no table. A table that holds
# only tables is the parent a dotted header implies, which ez never writes a
# pair into; old ledgers and locks name no such table, so it is no section.
# (segs arrive innermost first, as `tables` builds them; the header reads
# them outermost first)
def sect.put(skip: Bool, +ps: List<&2, Kv>, +segs: List<&2, String>) -> List<&2, Sect>:
  match skip:
    case True{}:
      []
    case False{}:
      [Sect{head.of(List.reverse(&2, String, segs)), ps}]

def sect.keep(+ps: List<&2, Kv>, parent: Bool, +segs: List<&2, String>) -> List<&2, Sect>:
  sect.put(Bool.and(List.is_empty(&2, Kv, ps), parent), ps, segs)

# a table's section, then the sections of the tables in it
def table.sects(+segs: List<&2, String>, +sub: List<&2, E.Val>, inner: List<&2, Sect>) -> List<&2, Sect>:
  List.append(&2, Sect, sect.keep(pairs.of(sub), has.table(sub), segs), inner)

# the sections of every table among a table's rows, in document order: each
# table's own section, then the tables in it, then the tables after it. The
# path to the table is kept innermost first, so a level prepends its name.
def tables(rows: List<&2, E.Val>, +segs: List<&2, String>) -> List<&2, Sect>:
  match rows:
    case []:
      []
    case E.VPair{name, E.VHead{_path, +sub}} <> tl:
      +at : List<&2, String> = name <> segs
      List.append(&2, Sect, table.sects(at, sub, tables(sub, at)), tables(tl, segs))
    case _hd <> tl:
      tables(tl, segs)

# a document eztoml read, as sections
def parse.of(+doc: E.Doc) -> Toml:
  +rows = E.root(doc)
  Toml{E.bad(doc), "", pairs.of(rows), tables(rows, [])}

# a document read from TOML text: eztoml's reading of it, as sections
def parse(text: String) -> Toml:
  parse.of(E.parse(text))

# ---------------------------------------------------------------------------
# for a test or a report

# a pair as `key=value`
def show.kv(kv: Kv) -> String:
  Kv{kk, vv} = kv
  kk ++ "=" ++ vv

# every pair of a section, shown
def show.kvs(ps: List<&2, Kv>) -> List<&2, String>:
  match ps:
    case []:
      []
    case hd <> tl:
      show.kv(hd) <> show.kvs(tl)

# a section as `name key=value ..`
def show.sect(sect: Sect) -> String:
  Sect{nn, ps} = sect
  String.join(nn <> show.kvs(ps), " ")

# every section of a document, shown
def show.sects(ss: List<&2, Sect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case hd <> tl:
      show.sect(hd) <> show.sects(tl)
