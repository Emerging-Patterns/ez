# manifest/toml: the slice of TOML the ledger and the lock need. A line is
# blank, a comment, a `[section]` header, or a `key = "value"` pair. A header is
# a dotted path whose segments may be quoted, and a key may be quoted, so a file
# path can be one. No arrays, no inline tables, no numbers, because every value
# ez writes is a string.
import Base

# a key and the string written for it
type Kv is Data:
  Kv{key: String, val: String}

# a section header and the pairs under it, in the order they were written
type Sect is Data:
  Sect{name: String, pairs: List<&2, Kv>}

# what one line turned out to be
type Line is Data:
  LSkip{}
  LHead{name: String}
  LPair{key: String, val: String}
  LBad{why: String}

# a trim in progress: `skip` is true until the first non-space, `out` is the
# chars kept so far, reversed
type Trim is Data:
  Trim{skip: Bool, out: List<&2, Char>}

# the sections read so far, and the first error if there was one. name is the
# section being filled, "" before any header; pairs and done are reversed.
type Toml is Data:
  Toml{bad: String, name: String, pairs: List<&2, Kv>, done: List<&2, Sect>}

# while skipping, a space is dropped and the skipping goes on; the first other
# char is kept and ends it
def trim.keep.go(sp: Bool, c: Char, out: List<&2, Char>) -> Trim:
  match sp:
    case True{}:
      Trim{True{}, out}
    case False{}:
      Trim{False{}, c <> out}

# a char offered to a trim that is still skipping. `+c` because the char is both
# asked about and kept; a fold's step may not take one, so it is split out here.
def trim.keep(+c: Char, out: List<&2, Char>) -> Trim:
  trim.keep.go(Char.is_space(c), c, out)

# one char of a trim: `skip` stays true until a non-space arrives
def trim.step(st: Trim, c: Char) -> Trim:
  Trim{skip, out} = st
  match skip:
    case True{}:
      trim.keep(c, out)
    case False{}:
      Trim{False{}, c <> out}

# the chars a finished trim collected. A destructure needs a parameter, never a
# local binder, so the fold's result comes in through one.
def trim.out(st: Trim) -> List<&2, Char>:
  Trim{_skip, out} = st
  out

# the chars with leading spaces dropped, reversed
def trim.pass(cs: List<&2, Char>) -> List<&2, Char>:
  trim.out(List.foldl(~&2, ~Char, ~Trim, ~trim.step, cs, Trim{True{}, []}))

# the string with no leading or trailing spaces. Two passes: the first reverses
# and drops what led, the second drops what trailed and puts it back in order.
def trim(s: String) -> String:
  String.from_list(trim.pass(trim.pass(String.to_list(s))))

# drops one leading char when it is the one given
def strip.cut(hit: Bool, h: Char, t: List<&2, Char>) -> List<&2, Char>:
  match hit:
    case True{}:
      t
    case False{}:
      h <> t

# the chars without one leading `c`, if there is one
def strip.front(cs: List<&2, Char>, c: Char) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +h <> t:
      strip.cut(Char.is_eq(h, c), h, t)

# the string without one leading `a` and one trailing `b`
def strip(s: String, a: Char, b: Char) -> String:
  +cs = strip.front(String.to_list(s), a)
  +rs = strip.front(List.reverse(&2, Char, cs), b)
  String.from_list(List.reverse(&2, Char, rs))

# a pair line, once it is known to hold an `=`: the key is what precedes the
# first one, the value everything after, so an `=` inside a value survives
def pair_of(parts: List<&2, String>) -> Line:
  match parts:
    case []:
      LBad{"an empty line cannot be a pair"}
    case h <> t:
      LPair{strip(trim(h), '"', '"'), strip(trim(String.join(t, "=")), '"', '"')}

# a header line, once it is known to start with `[`
def head_of(+s: String, shut: Bool) -> Line:
  match shut:
    case True{}:
      LHead{strip(s, '[', ']')}
    case False{}:
      LBad{s ++ " is not a section header"}

# what a trimmed line is. The order matters: a comment may hold anything.
def line_of(+s: String) -> Line:
  Bool.pick(Line, String.is_empty(s), LSkip{},
    Bool.pick(Line, String.starts_with(s, "#"), LSkip{},
      Bool.pick(Line, String.starts_with(s, "["), head_of(s, String.ends_with(s, "]")),
        Bool.pick(Line, String.contains(s, "="), pair_of(String.split(s, '=')),
          LBad{s ++ " is neither a section header nor a key"}))))

# the first error wins, so a later one is dropped
def first(+bad: String, why: String) -> String:
  Bool.pick(String, String.is_empty(bad), why, bad)

# the section being filled, moved into the finished ones. A header with no pairs
# is still a section; only the "" before the first header is not.
def flush.put(empty: Bool, name: String, pairs: List<&2, Kv>, done: List<&2, Sect>) -> List<&2, Sect>:
  match empty:
    case True{}:
      done
    case False{}:
      Sect{name, List.reverse(&2, Kv, pairs)} <> done

# the section being filled, moved into the finished ones
def flush(+name: String, pairs: List<&2, Kv>, done: List<&2, Sect>) -> List<&2, Sect>:
  flush.put(String.is_empty(name), name, pairs, done)

# a pair belongs to the section being filled, and is an error before the first
# header
def put.go(loose: Bool, bad: String, name: String, pairs: List<&2, Kv>,
  done: List<&2, Sect>, +key: String, val: String) -> Toml:
  match loose:
    case True{}:
      Toml{first(bad, key ++ " = is outside any section"), name, pairs, done}
    case False{}:
      Toml{bad, name, Kv{key, val} <> pairs, done}

# a pair belongs to the section being filled, and is an error before the first
# header
def put(st: Toml, key: String, val: String) -> Toml:
  Toml{bad, +name, pairs, done} = st
  put.go(String.is_empty(name), bad, name, pairs, done, key, val)

# the state once a line has been classified
def step.go(st: Toml, line: Line) -> Toml:
  Toml{bad, name, pairs, done} = st
  match line:
    case LSkip{}:
      Toml{bad, name, pairs, done}
    case LHead{next}:
      Toml{bad, next, [], flush(name, pairs, done)}
    case LPair{key, val}:
      put(Toml{bad, name, pairs, done}, key, val)
    case LBad{why}:
      Toml{first(bad, why), name, pairs, done}

# one line against the state
def step(st: Toml, raw: String) -> Toml:
  step.go(st, line_of(trim(raw)))

# the last section flushed, and the finished ones put back in order
def parse.fin(r: Toml) -> Toml:
  Toml{bad, name, pairs, done} = r
  Toml{bad, "", [], List.reverse(&2, Sect, flush(name, pairs, done))}

# the sections of a document, and the first error if there was one
def parse(text: String) -> Toml:
  parse.fin(List.foldl(~&2, ~String, ~Toml, ~step, String.lines(text), Toml{"", "", [], []}))

# this pair's value when the key matches, otherwise whatever the rest of the
# table gave
def value.at(kv: Kv, rest: String, key: String) -> String:
  Kv{k, v} = kv
  Bool.pick(String, String.eq(k, key), v, rest)

# the value written for a key in a table, or "" when it is absent. The scan
# recurses first and picks after, so no recursive call hides inside a branch.
def value(pairs: List<&2, Kv>, +key: String) -> String:
  match pairs:
    case []:
      ""
    case h <> t:
      value.at(h, value(t, key), key)

# the sections a parse found, in the order they were written
def sects(t: Toml) -> List<&2, Sect>:
  Toml{_bad, _name, _pairs, done} = t
  done

# what a header's next character is: the quoting toggles, an unquoted dot cuts,
# anything else is kept
type Sym is Data:
  SQuote{}
  SDot{}
  SKeep{c: Char}

# a header char classified. `+c` because it is both asked about and kept.
def seg.sym(+c: Char) -> Sym:
  Bool.pick(Sym, Char.is_eq(c, '"'), SQuote{},
    Bool.pick(Sym, Char.is_eq(c, '.'), SDot{}, SKeep{c}))

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
def seg.go(st: Split, s: Sym) -> Split:
  Split{quoted, cur, out} = st
  match s:
    case SQuote{}:
      Split{Bool.not(quoted), cur, out}
    case SDot{}:
      seg.dot(quoted, cur, out)
    case SKeep{c}:
      Split{quoted, c <> cur, out}

# one char of a header against the state
def seg.step(st: Split, c: Char) -> Split:
  seg.go(st, seg.sym(c))

# the segment still being gathered, closed, and the rest put back in order
def seg.fin(st: Split) -> List<&2, String>:
  Split{_quoted, cur, out} = st
  List.reverse(&2, String, seg.done(cur) <> out)

# a header's segments, unquoted. `packages."0x0a".files` is three of them, and a
# quoted segment may hold the dots a bare one may not.
def segments(s: String) -> List<&2, String>:
  seg.fin(List.foldl(~&2, ~Char, ~Split, ~seg.step, String.to_list(s),
    Split{False{}, [], []}))

# a string in quotes, which is how a segment or a key that is not bare is
# written, and how every value is
def quote(+s: String) -> String:
  "\"" ++ s ++ "\""

# a char a bare key may hold. `+c` because it is asked four questions; a
# predicate handed to a fold may not take one, so it is split out here.
def bare.at(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c),
    Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '-'))))

# a char a bare key may hold
def bare.ok(c: Char) -> Bool:
  bare.at(c)

# whether a key can be written without quotes
def bare(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)),
    List.all(~&2, ~Char, ~bare.ok, String.to_list(s)))

# a key as it is written: bare when it can be, quoted when it must be
def key(+s: String) -> String:
  Bool.pick(String, bare(s), s, quote(s))

# one `key = "value"` line
def render.pair(kv: Kv) -> String:
  Kv{k, v} = kv
  key(k) ++ " = " ++ quote(v) ++ "\n"

# every pair of a section, in the order it holds them
def render.pairs(ps: List<&2, Kv>) -> String:
  match ps:
    case []:
      ""
    case h <> t:
      render.pair(h) ++ render.pairs(t)

# one table: its header, then its pairs. The header is written as it is given,
# so a caller that needs a quoted segment quotes it.
def render.sect(s: Sect) -> String:
  Sect{n, ps} = s
  "[" ++ n ++ "]\n" ++ render.pairs(ps)

# every table of a document
def render.all(ss: List<&2, Sect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case h <> t:
      render.sect(h) <> render.all(t)

# a document of tables, one blank line between them
def render(ss: List<&2, Sect>) -> String:
  String.join(render.all(ss), "\n")

# a pair as `key=value`, for a test or a report
def show.kv(kv: Kv) -> String:
  Kv{k, v} = kv
  k ++ "=" ++ v

# every pair of a section, shown
def show.kvs(ps: List<&2, Kv>) -> List<&2, String>:
  match ps:
    case []:
      []
    case h <> t:
      show.kv(h) <> show.kvs(t)

# a section as `name key=value ..`
def show.sect(s: Sect) -> String:
  Sect{n, ps} = s
  String.join(n <> show.kvs(ps), " ")

# every section of a document, shown
def show.sects(ss: List<&2, Sect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case h <> t:
      show.sect(h) <> show.sects(t)
