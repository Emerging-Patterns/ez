# check/body: the body of a publish read the way the hub reads it, for
# check/oracle.bend. bend sends `{"files": {..}, "nonce": N}`; this is the
# reading of that object into the files it carries, their order, their
# manifest and the `0x` name it gives them. It is pure, so a law reaches it
# without the oracle's sockets, and nothing here is part of ez: it is the
# test hub's own reading, and a body it only half understands is refused.
import Base
import ../share/sha.bend as Sha
import ./serve.bend as S

# a list with its last element gone, the head held back one step so the walk can
# see whether it is looking at the last one. The list comes first because a
# self-call must shrink an argument before it changes one.
def init.put(rest: List<&2, String>, held: String) -> List<&2, String>:
  match rest:
    case []:
      []
    case h2 <> t2:
      held <> init.put(t2, h2)

# every element but the last
def init.of(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case []:
      []
    case h <> t:
      init.put(t, h)

# the directory a path lies in
def parent.of(path: String) -> String:
  String.join(init.of(String.split(path, '/')), "/")

# one step of the skip, with the head's answer in hand. A recursive call in an
# arm of a `Bool.pick` is not an arm: `Bool.pick` is an ordinary function and
# builds both before it picks one, so the first non-space still cost a walk of
# everything after it. The rest arrives as a thunk and only the arm that wants
# it applies it.
def ws.step(space: Bool, ch: Char, tail: String, rest: Unit -> String) -> String:
  match space:
    case True{}:
      rest(Unit{})
    case False{}:
      SCon{ch, tail}

# the text with its leading whitespace gone
def ws(text: String) -> String:
  match text:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ws.step(Char.is_space(c), c, t, _u => ws(t))

# a character that had to be there, either consumed or refused
def eat.at(ok: Bool, rest: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{rest}
    case False{}:
      None{}

# the text after a character that must head it, or nothing when it does not
def eat(+text: String, ch: Char) -> Maybe<&2, String>:
  eat.at(String.starts_with(text, Char.show(ch)), String.drop(text, 1n))

# a hex digit's value, or nothing when the character is not one
def hex.val(+ch: Char) -> Maybe<&2, U32>:
  +x = Char.to_u32(ch)
  Bool.pick(Maybe<&2, U32>, Char.is_digit(ch), Some{U32.sub(x, 48)},
    Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)),
      Some{U32.sub(x, 87)},
      Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)),
        Some{U32.sub(x, 55)},
        None{})))

# a code point this oracle will put in a file. A Bend source file is ASCII, and
# a guess at what a higher code point should become would corrupt the file
# rather than fail, so nothing above 0x7f is accepted.
def hex.small(+code: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_lt(code, 128), Some{code}, None{})

# two digit values as one byte
def hex.join(high: Maybe<&2, U32>, low: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match high low:
    case Some{x} Some{y}:
      Some{U32.add(U32.mul(x, 16), y)}
    case Some{x} None{}:
      None{}
    case None{} _m:
      None{}

# the byte two hex characters spell
def hex.pair(high: Maybe<&2, Char>, low: Maybe<&2, Char>) -> Maybe<&2, U32>:
  match high low:
    case Some{x} Some{y}:
      hex.join(hex.val(x), hex.val(y))
    case Some{x} None{}:
      None{}
    case None{} _m:
      None{}

# two bytes as one code point, the high one first, refused when it is not ASCII
def hex.wide(high: Maybe<&2, U32>, low: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match high low:
    case Some{x} Some{y}:
      hex.small(U32.add(U32.mul(x, 256), y))
    case Some{x} None{}:
      None{}
    case None{} _m:
      None{}

# one character of a string, decoded from the escape that spelled it, and what
# follows it
type Esc is Data:
  EBad{why: String}
  EOk{c: Char, rest: String}

# a `\uXXXX` escape's verdict
def esc.u.fin(code: Maybe<&2, U32>, rest: String) -> Esc:
  match code:
    case None{}:
      EBad{"a unicode escape that is not four hex digits below 0080"}
    case Some{x}:
      EOk{Chr{x}, rest}

# the character a `\uXXXX` escape names, read from just after the `u`
def esc.u(+text: String) -> Esc:
  esc.u.fin(
    hex.wide(hex.pair(String.get(text, 0n), String.get(text, 1n)),
      hex.pair(String.get(text, 2n), String.get(text, 3n))),
    String.drop(text, 4n))

# the character a backslash introduces, read from just after it. An escape this
# oracle does not know is refused, never passed through: a body half understood
# would write a file that is not the one that was published.
def esc.of(text: String) -> Esc:
  match text:
    case SNil{}:
      EBad{"a backslash at the end of the body"}
    case SCon{+c, +t}:
      Bool.pick(Esc, Char.is_eq(c, '"'), EOk{'"', t},
        Bool.pick(Esc, Char.is_eq(c, '\\'), EOk{'\\', t},
          Bool.pick(Esc, Char.is_eq(c, '/'), EOk{'/', t},
            Bool.pick(Esc, Char.is_eq(c, 'n'), EOk{'\n', t},
              Bool.pick(Esc, Char.is_eq(c, 't'), EOk{'\t', t},
                Bool.pick(Esc, Char.is_eq(c, 'r'), EOk{'\r', t},
                  Bool.pick(Esc, Char.is_eq(c, 'b'), EOk{Chr{8}, t},
                    Bool.pick(Esc, Char.is_eq(c, 'f'), EOk{Chr{12}, t},
                      Bool.pick(Esc, Char.is_eq(c, 'u'), esc.u(t),
                        EBad{"an escape this oracle does not know"})))))))))

# a span of a body with its escapes decoded, or the reason one could not be
type Uns is Data:
  UBad{why: String}
  UOk{text: String}

# the next character of a span, whether a backslash spelled it or it stood for
# itself. Both are decided here so the walk below has one recursive call and not
# two, which would make it read the rest of the span twice over at every step.
def uns.step(esc: Bool, ch: Char, tail: String) -> Esc:
  match esc:
    case True{}:
      esc.of(tail)
    case False{}:
      EOk{ch, tail}

# what is left of a span after one character of it
def uns.rest(step: Esc) -> String:
  match step:
    case EBad{_why}:
      SNil{}
    case EOk{_c, r}:
      r

# a character put in front of what came after it
def uns.push(ch: Char, acc: Uns) -> Uns:
  match acc:
    case UBad{why}:
      UBad{why}
    case UOk{text}:
      UOk{SCon{ch, text}}

# one decoded character joined to the rest, an escape that failed carrying its
# reason out past everything after it
def uns.put(step: Esc, acc: Uns) -> Uns:
  match step:
    case EBad{why}:
      UBad{why}
    case EOk{c, _rest}:
      uns.push(c, acc)

# a span of a body decoded. The fuel is the span's own length: every step eats
# at least one character, so it cannot run out early, and the walk needs it
# because an escape makes the step shorter than the string it left behind.
def unesc(fuel: Nat, span: String) -> Uns:
  match fuel span:
    case 0n SNil{}:
      UOk{""}
    case 0n SCon{_c, _t}:
      UBad{"a span longer than the length it was cut to"}
    case 1n+f SNil{}:
      UOk{""}
    case 1n+f SCon{+c, t}:
      +e = uns.step(Char.is_eq(c, '\\'), c, t)
      uns.put(e, unesc(f, uns.rest(e)))

# a string literal read out of a body: its text, and what follows its closing
# quote
type Str is Data:
  SBad{why: String}
  SOk{text: String, rest: String}

# one step of the measure, with the answer to "does this quote close it" in
# hand. Under a `Bool.pick` the closing quote still cost a walk of the rest of
# the body, and a `Succ` built over every character of it.
def str.end.step(shut: Bool, rest: Unit -> Nat) -> Nat:
  match shut:
    case True{}:
      0n
    case False{}:
      rest(Unit{})

# how many characters lie before the quote that closes a string literal, or the
# whole length when none does. `esc` says a backslash stood before this
# character, so this one cannot close the literal and cannot escape the next.
def str.end(text: String, +esc: Bool) -> Nat:
  match text:
    case SNil{}:
      0n
    case SCon{+c, t}:
      str.end.step(Bool.and(Bool.not(esc), Char.is_eq(c, '"')),
        _u => Succ{str.end(t, Bool.and(Bool.not(esc), Char.is_eq(c, '\\')))})

# a literal whose span decoded, or the escape that stopped it
def str.done(unescaped: Uns, rest: String) -> Str:
  match unescaped:
    case UBad{why}:
      SBad{why}
    case UOk{text}:
      SOk{text, rest}

# a literal that ran off the end of the body is refused rather than taken for
# whatever was left
def str.fin(closed: Bool, unescaped: Uns, rest: String) -> Str:
  match closed:
    case False{}:
      SBad{"a string in the body has no closing quote"}
    case True{}:
      str.done(unescaped, rest)

# the span up to the closing quote decoded, and the body past that quote
def str.cut(+len: Nat, +text: String) -> Str:
  str.fin(Maybe.is_some(&2, Char, String.get(text, len)),
    unesc(len, String.take(text, len)), String.drop(text, Succ{len}))

# a string literal read from just after its opening quote
def str.of(+text: String) -> Str:
  str.cut(str.end(text, False{}), text)

# one file of a package: where it sits in the package, and what is in it
type Ent is Data:
  Ent{path: String, text: String}

# where a file sits
def ent.path(entry: Ent) -> String:
  Ent{p, _t} = entry
  p

# the order the manifest lists files in, which is ascending by path
def ent.le(left: Ent, right: Ent) -> Bool:
  String.is_le(ent.path(left), ent.path(right))

# the files in the order a manifest names them
def sorted(es: List<&2, Ent>) -> List<&2, Ent>:
  List.sort(~Ent, ~ent.le, es)

# a manifest line: a file's digest, a space, its path
def line.of(entry: Ent) -> String:
  Ent{p, t} = entry
  Sha.hex(t) ++ " " ++ p ++ "\n"

# the manifest: a line for each file, in the order they were given
def manifest.of(es: List<&2, Ent>) -> String:
  match es:
    case []:
      ""
    case h <> t:
      line.of(h) ++ manifest.of(t)

# the `0x` name a manifest gives its package: the first 32 hex characters of the
# manifest's digest
def hash.of(content: String) -> String:
  "0x" ++ String.take(Sha.hex(content), 32n)

# one `"path": "contents"` pair of the files object, or the end of that object
type Mem is Data:
  MBad{why: String}
  MEnd{}
  MOne{path: String, text: String, more: Bool, rest: String}

# a comma means another pair follows, a brace ends the object
def mem.tail.at(+path: String, +text: String, +sep: String, +rest: String) -> Mem:
  Bool.pick(Mem, String.eq(sep, ","), MOne{path, text, True{}, rest},
    Bool.pick(Mem, String.eq(sep, "}"), MOne{path, text, False{}, rest},
      MBad{"a files entry followed by neither a comma nor a brace"}))

# what stands after a pair
def mem.tail(path: String, text: String, +after: String) -> Mem:
  mem.tail.at(path, text, String.take(after, 1n), String.drop(after, 1n))

# a pair whose value has been read
def mem.val(path: String, value: Str) -> Mem:
  match value:
    case SBad{why}:
      MBad{why}
    case SOk{text, rest}:
      mem.tail(path, text, ws(rest))

# a value that is not a string is refused: the files object holds file contents
# and nothing else
def mem.quote.at(path: String, ok: Bool, rest: String) -> Mem:
  match ok:
    case False{}:
      MBad{"a files entry whose value is not a string"}
    case True{}:
      mem.val(path, str.of(rest))

# the quote that opens a value
def mem.quote(path: String, +text: String) -> Mem:
  mem.quote.at(path, String.starts_with(text, "\""), String.drop(text, 1n))

# the colon between a key and its value
def mem.colon(path: String, after: Maybe<&2, String>) -> Mem:
  match after:
    case None{}:
      MBad{"a files entry with no colon after its key"}
    case Some{t}:
      mem.quote(path, ws(t))

# a pair whose key has been read
def mem.key(key: Str) -> Mem:
  match key:
    case SBad{why}:
      MBad{why}
    case SOk{path, rest}:
      mem.colon(path, eat(ws(rest), ':'))

# the quote that opens a key
def mem.one.key(ok: Bool, rest: String) -> Mem:
  match ok:
    case False{}:
      MBad{"a files entry that does not begin with a key"}
    case True{}:
      mem.key(str.of(rest))

# the end of the object, decided. The pair reader hangs off the other arm
# rather than sitting in an argument, so an object that has ended does not
# read a pair out of what follows it.
def mem.one.shut(end: Bool, +text: String) -> Mem:
  match end:
    case True{}:
      MEnd{}
    case False{}:
      mem.one.key(String.starts_with(text, "\""), String.drop(text, 1n))

# either the brace that ends the object or the pair that continues it
def mem.one.at(+text: String) -> Mem:
  mem.one.shut(String.starts_with(text, "}"), text)

# the next pair of the files object, read from wherever the last one left off
def mem.one(text: String) -> Mem:
  mem.one.at(ws(text))

# every file a body carried, or the reason the body could not be read
type Obj is Data:
  OBad{why: String}
  OOk{items: List<&2, Ent>}

# a pair the object goes on past, or the end of it
def obj.rest.if(more: Bool, rest: String) -> String:
  match more:
    case True{}:
      rest
    case False{}:
      SNil{}

# where the walk picks up after a pair
def obj.rest(member: Mem) -> String:
  match member:
    case MBad{_why}:
      SNil{}
    case MEnd{}:
      SNil{}
    case MOne{_p, _t, more, rest}:
      obj.rest.if(more, rest)

# one file joined to the ones after it
def obj.cons(entry: Ent, tail: Obj) -> Obj:
  match tail:
    case OBad{why}:
      OBad{why}
    case OOk{items}:
      OOk{entry <> items}

# the last pair of an object closes it, and what the walk found past it is not
# part of the body
def obj.put.if(more: Bool, entry: Ent, tail: Obj) -> Obj:
  match more:
    case True{}:
      obj.cons(entry, tail)
    case False{}:
      OOk{[entry]}

# a pair joined to whatever the rest of the object gave
def obj.put(member: Mem, tail: Obj) -> Obj:
  match member:
    case MBad{why}:
      OBad{why}
    case MEnd{}:
      OOk{[]}
    case MOne{p, t, more, _rest}:
      obj.put.if(more, Ent{p, t}, tail)

# every pair of the files object. The fuel is the body's length, which no object
# can hold more pairs than.
def obj.go(fuel: Nat, text: String) -> Obj:
  match fuel:
    case 0n:
      OBad{"a files object that never ends"}
    case 1n+f:
      +m = mem.one(text)
      obj.put(m, obj.go(f, obj.rest(m)))

# the files object itself
def parse.body(fuel: Nat, after: Maybe<&2, String>) -> Obj:
  match after:
    case None{}:
      OBad{"a files key whose value is not an object"}
    case Some{t}:
      obj.go(fuel, t)

# the colon after the files key
def parse.colon(fuel: Nat, after: Maybe<&2, String>) -> Obj:
  match after:
    case None{}:
      OBad{"no colon after the files key"}
    case Some{t}:
      parse.body(fuel, eat(ws(t), '{'))

# bend sends `{"files": {..}, "nonce": N}` and this oracle reads exactly that.
# A body in another shape is refused rather than searched, because a body it
# only half understood would publish a package that is not the one that was sent.
def parse.name.if(fuel: Nat, ok: Bool, text: String) -> Obj:
  match ok:
    case False{}:
      OBad{"a body whose first key is not files"}
    case True{}:
      parse.colon(fuel, eat(text, ':'))

# the body's first key
def parse.name(fuel: Nat, key: Str) -> Obj:
  match key:
    case SBad{why}:
      OBad{why}
    case SOk{name, rest}:
      parse.name.if(fuel, String.eq(name, "files"), ws(rest))

# the quote that opens the body's first key
def parse.quote.at(fuel: Nat, ok: Bool, rest: String) -> Obj:
  match ok:
    case False{}:
      OBad{"a body with no key"}
    case True{}:
      parse.name(fuel, str.of(rest))

# the key that follows the body's opening brace
def parse.quote(fuel: Nat, +text: String) -> Obj:
  parse.quote.at(fuel, String.starts_with(text, "\""), String.drop(text, 1n))

# the body's opening brace
def parse.open(fuel: Nat, after: Maybe<&2, String>) -> Obj:
  match after:
    case None{}:
      OBad{"a body that is not an object"}
    case Some{t}:
      parse.quote(fuel, ws(t))

# the files a request body carries, as (path, contents) pairs. The fuel counts
# the pairs the body could hold at most: the shortest one a body can spell is
# `"":"",` and no count of them is ever reached, but the walk below reads both
# arms of its choice, so a fuel of the body's whole length would be a walk of
# the body's whole length past its end.
def parse(+body: String) -> Obj:
  parse.open(U32.to_nat(U32.add(U32.div(S.size(body), 6), 8)), eat(ws(body), '{'))
