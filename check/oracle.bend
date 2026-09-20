# check/oracle: a local stand-in for the package hub, so `bend --publish` can be
# run without touching hub.bend-lang.com. It accepts the POST, computes the
# package hash the way cli_publish does, writes the package out, and answers
# with that hash, which is what bend checks the response against. Anything that
# is not a POST is a file served out of the same directory, so a published
# package can be fetched back.
#
#   bend check/oracle.bend <dir> <port>
#
# What is here is the hub: the reading of a body is pure and sits above, the
# sockets and the writing are below, and nothing in the upper half touches IO.
# Reading a request off a socket and writing an answer back are check/serve.bend,
# shared with check/framing.bend. Plaintext HTTP only; bend speaks TLS to the
# real hub, and run/run.bend explains why a Bend binary cannot.
#
# `GET /` answers `ok`, so a script can wait for the oracle before it publishes.
# One connection is served at a time, each answer states its length and closes
# the socket, and the oracle stops of its own accord after a million of them.
import Base
import ../sha/sha.bend as Sha
import ../io/file.bend as F
import ../run/run.bend as R
import ./serve.bend as S

# a list with its last element gone, the head held back one step so the walk can
# see whether it is looking at the last one. The list comes first because a
# self-call must shrink an argument before it changes one.
def init.put(t: List<&2, String>, h: String) -> List<&2, String>:
  match t:
    case []:
      []
    case h2 <> t2:
      h <> init.put(t2, h2)

# every element but the last
def init.of(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case []:
      []
    case h <> t:
      init.put(t, h)

# the directory a path lies in
def parent.of(p: String) -> String:
  String.join(init.of(String.split(p, '/')), "/")

# the text with its leading whitespace gone
def ws(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      Bool.pick(String, Char.is_space(c), ws(t), SCon{c, t})

# a character that had to be there, either consumed or refused
def eat.at(ok: Bool, rest: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{rest}
    case False{}:
      None{}

# the text after a character that must head it, or nothing when it does not
def eat(+s: String, c: Char) -> Maybe<&2, String>:
  eat.at(String.starts_with(s, Char.show(c)), String.drop(s, 1n))

# a hex digit's value, or nothing when the character is not one
def hex.val(+c: Char) -> Maybe<&2, U32>:
  +x = Char.to_u32(c)
  Bool.pick(Maybe<&2, U32>, Char.is_digit(c), Some{U32.sub(x, 48)},
    Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)),
      Some{U32.sub(x, 87)},
      Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)),
        Some{U32.sub(x, 55)},
        None{})))

# a code point this oracle will put in a file. A Bend source file is ASCII, and
# a guess at what a higher code point should become would corrupt the file
# rather than fail, so nothing above 0x7f is accepted.
def hex.small(+x: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_lt(x, 128), Some{x}, None{})

# two digit values as one byte
def hex.join(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a b:
    case Some{x} Some{y}:
      Some{U32.add(U32.mul(x, 16), y)}
    case Some{x} None{}:
      None{}
    case None{} _m:
      None{}

# the byte two hex characters spell
def hex.pair(a: Maybe<&2, Char>, b: Maybe<&2, Char>) -> Maybe<&2, U32>:
  match a b:
    case Some{x} Some{y}:
      hex.join(hex.val(x), hex.val(y))
    case Some{x} None{}:
      None{}
    case None{} _m:
      None{}

# two bytes as one code point, the high one first, refused when it is not ASCII
def hex.wide(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a b:
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
def esc.u.fin(v: Maybe<&2, U32>, rest: String) -> Esc:
  match v:
    case None{}:
      EBad{"a unicode escape that is not four hex digits below 0080"}
    case Some{x}:
      EOk{Chr{x}, rest}

# the character a `\uXXXX` escape names, read from just after the `u`
def esc.u(+s: String) -> Esc:
  esc.u.fin(
    hex.wide(hex.pair(String.get(s, 0n), String.get(s, 1n)),
      hex.pair(String.get(s, 2n), String.get(s, 3n))),
    String.drop(s, 4n))

# the character a backslash introduces, read from just after it. An escape this
# oracle does not know is refused, never passed through: a body half understood
# would write a file that is not the one that was published.
def esc.of(s: String) -> Esc:
  match s:
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
def uns.step(esc: Bool, c: Char, t: String) -> Esc:
  match esc:
    case True{}:
      esc.of(t)
    case False{}:
      EOk{c, t}

# what is left of a span after one character of it
def uns.rest(e: Esc) -> String:
  match e:
    case EBad{_why}:
      SNil{}
    case EOk{_c, r}:
      r

# a character put in front of what came after it
def uns.push(c: Char, r: Uns) -> Uns:
  match r:
    case UBad{why}:
      UBad{why}
    case UOk{text}:
      UOk{SCon{c, text}}

# one decoded character joined to the rest, an escape that failed carrying its
# reason out past everything after it
def uns.put(e: Esc, r: Uns) -> Uns:
  match e:
    case EBad{why}:
      UBad{why}
    case EOk{c, _rest}:
      uns.push(c, r)

# a span of a body decoded. The fuel is the span's own length: every step eats
# at least one character, so it cannot run out early, and the walk needs it
# because an escape makes the step shorter than the string it left behind.
def unesc(fuel: Nat, s: String) -> Uns:
  match fuel s:
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

# how many characters lie before the quote that closes a string literal, or the
# whole length when none does. `esc` says a backslash stood before this
# character, so this one cannot close the literal and cannot escape the next.
def str.end(s: String, +esc: Bool) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+c, t}:
      Bool.pick(Nat, Bool.and(Bool.not(esc), Char.is_eq(c, '"')), 0n,
        Succ{str.end(t, Bool.and(Bool.not(esc), Char.is_eq(c, '\\')))})

# a literal whose span decoded, or the escape that stopped it
def str.done(u: Uns, rest: String) -> Str:
  match u:
    case UBad{why}:
      SBad{why}
    case UOk{text}:
      SOk{text, rest}

# a literal that ran off the end of the body is refused rather than taken for
# whatever was left
def str.fin(closed: Bool, u: Uns, rest: String) -> Str:
  match closed:
    case False{}:
      SBad{"a string in the body has no closing quote"}
    case True{}:
      str.done(u, rest)

# the span up to the closing quote decoded, and the body past that quote
def str.cut(+n: Nat, +s: String) -> Str:
  str.fin(Maybe.is_some(&2, Char, String.get(s, n)),
    unesc(n, String.take(s, n)), String.drop(s, Succ{n}))

# a string literal read from just after its opening quote
def str.of(+s: String) -> Str:
  str.cut(str.end(s, False{}), s)

# one file of a package: where it sits in the package, and what is in it
type Ent is Data:
  Ent{path: String, text: String}

# where a file sits
def ent.path(e: Ent) -> String:
  Ent{p, _t} = e
  p

# the order the manifest lists files in, which is ascending by path
def ent.le(a: Ent, b: Ent) -> Bool:
  String.is_le(ent.path(a), ent.path(b))

# the files in the order a manifest names them
def sorted(es: List<&2, Ent>) -> List<&2, Ent>:
  List.sort(~Ent, ~ent.le, es)

# a manifest line: a file's digest, a space, its path
def line.of(e: Ent) -> String:
  Ent{p, t} = e
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
def hash.of(m: String) -> String:
  "0x" ++ String.take(Sha.hex(m), 32n)

# one `"path": "contents"` pair of the files object, or the end of that object
type Mem is Data:
  MBad{why: String}
  MEnd{}
  MOne{path: String, text: String, more: Bool, rest: String}

# a comma means another pair follows, a brace ends the object
def mem.tail.at(+path: String, +text: String, +c: String, +rest: String) -> Mem:
  Bool.pick(Mem, String.eq(c, ","), MOne{path, text, True{}, rest},
    Bool.pick(Mem, String.eq(c, "}"), MOne{path, text, False{}, rest},
      MBad{"a files entry followed by neither a comma nor a brace"}))

# what stands after a pair
def mem.tail(path: String, text: String, +s: String) -> Mem:
  mem.tail.at(path, text, String.take(s, 1n), String.drop(s, 1n))

# a pair whose value has been read
def mem.val(path: String, v: Str) -> Mem:
  match v:
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
def mem.quote(path: String, +s: String) -> Mem:
  mem.quote.at(path, String.starts_with(s, "\""), String.drop(s, 1n))

# the colon between a key and its value
def mem.colon(path: String, m: Maybe<&2, String>) -> Mem:
  match m:
    case None{}:
      MBad{"a files entry with no colon after its key"}
    case Some{t}:
      mem.quote(path, ws(t))

# a pair whose key has been read
def mem.key(k: Str) -> Mem:
  match k:
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

# either the brace that ends the object or the pair that continues it
def mem.one.at(+s: String) -> Mem:
  Bool.pick(Mem, String.starts_with(s, "}"), MEnd{},
    mem.one.key(String.starts_with(s, "\""), String.drop(s, 1n)))

# the next pair of the files object, read from wherever the last one left off
def mem.one(s: String) -> Mem:
  mem.one.at(ws(s))

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
def obj.rest(m: Mem) -> String:
  match m:
    case MBad{_why}:
      SNil{}
    case MEnd{}:
      SNil{}
    case MOne{_p, _t, more, rest}:
      obj.rest.if(more, rest)

# one file joined to the ones after it
def obj.cons(e: Ent, o: Obj) -> Obj:
  match o:
    case OBad{why}:
      OBad{why}
    case OOk{items}:
      OOk{e <> items}

# the last pair of an object closes it, and what the walk found past it is not
# part of the body
def obj.put.if(more: Bool, e: Ent, o: Obj) -> Obj:
  match more:
    case True{}:
      obj.cons(e, o)
    case False{}:
      OOk{[e]}

# a pair joined to whatever the rest of the object gave
def obj.put(m: Mem, o: Obj) -> Obj:
  match m:
    case MBad{why}:
      OBad{why}
    case MEnd{}:
      OOk{[]}
    case MOne{p, t, more, _rest}:
      obj.put.if(more, Ent{p, t}, o)

# every pair of the files object. The fuel is the body's length, which no object
# can hold more pairs than.
def obj.go(fuel: Nat, s: String) -> Obj:
  match fuel:
    case 0n:
      OBad{"a files object that never ends"}
    case 1n+f:
      +m = mem.one(s)
      obj.put(m, obj.go(f, obj.rest(m)))

# the files object itself
def parse.body(fuel: Nat, m: Maybe<&2, String>) -> Obj:
  match m:
    case None{}:
      OBad{"a files key whose value is not an object"}
    case Some{t}:
      obj.go(fuel, t)

# the colon after the files key
def parse.colon(fuel: Nat, m: Maybe<&2, String>) -> Obj:
  match m:
    case None{}:
      OBad{"no colon after the files key"}
    case Some{t}:
      parse.body(fuel, eat(ws(t), '{'))

# bend sends `{"files": {..}, "nonce": N}` and this oracle reads exactly that.
# A body in another shape is refused rather than searched, because a body it
# only half understood would publish a package that is not the one that was sent.
def parse.name.if(fuel: Nat, ok: Bool, s: String) -> Obj:
  match ok:
    case False{}:
      OBad{"a body whose first key is not files"}
    case True{}:
      parse.colon(fuel, eat(s, ':'))

# the body's first key
def parse.name(fuel: Nat, k: Str) -> Obj:
  match k:
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
def parse.quote(fuel: Nat, +s: String) -> Obj:
  parse.quote.at(fuel, String.starts_with(s, "\""), String.drop(s, 1n))

# the body's opening brace
def parse.open(fuel: Nat, m: Maybe<&2, String>) -> Obj:
  match m:
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

# one answer written and the connection closed. Every answer states its length
# and says the connection closes, because bend, curl and nix's fetcher all read
# a body to the length they were promised and then expect the socket to shut.
def answer(sock: Socket, status: String, body: String) -> IO(Unit):
  S.answer(sock, S.response(status, body))

# a file that was there, or the 404 for one that was not
def serve.file(sock: Socket, m: Maybe<&2, String>) -> IO(Unit):
  match m:
    case None{}:
      answer(sock, "404 Not Found", "")
    case Some{text}:
      answer(sock, "200 OK", text)

# the file a request path names under the served directory
def serve.get(sock: Socket, dir: String, path: String) -> IO(Unit):
  do IO<Unit>:
    m : Maybe<&2, String> <- F.read(dir ++ path)
    serve.file(sock, m)

# `/` answers `ok` so a caller can wait for the oracle to come up before it
# publishes anything. Nothing is published at the root, so nothing is shadowed.
def get.go(root: Bool, sock: Socket, dir: String, path: String) -> IO(Unit):
  match root:
    case True{}:
      answer(sock, "200 OK", "ok")
    case False{}:
      serve.get(sock, dir, path)

# a file written once its directory exists
def write.after(out: String, at: String, text: String) -> IO(Bool):
  do IO<Bool>:
    ok : Bool <- F.write(at, text)
    return Bool.and(R.ok(out), ok)

# one file written, with its parent directories made first. Base has no mkdir,
# so run/run.bend runs one.
def write.file(+at: String, text: String) -> IO(Bool):
  do IO<Bool>:
    out : String <- R.exec(["mkdir", "-p", parent.of(at)])
    write.after(out, at, text)

# one file of a package written under the package's directory
def write.ent(dir: String, e: Ent) -> IO(Bool):
  Ent{p, t} = e
  write.file(dir ++ "/" ++ p, t)

# every file of a package written
def write.all(+dir: String, es: List<&2, Ent>) -> IO(Bool):
  match es:
    case []:
      IO.pure(Bool, True{})
    case h <> t:
      do IO<Bool>:
        a : Bool <- write.ent(dir, h)
        b : Bool <- write.all(dir, t)
        return Bool.and(a, b)

# a package that could not be written is a 500, so a test sees the failure here
# rather than in a hash that does not match
def post.said(sock: Socket, ok: Bool, h: String) -> IO(Unit):
  match ok:
    case True{}:
      answer(sock, "200 OK", h)
    case False{}:
      answer(sock, "500 Internal Server Error", "the package could not be written")

# the package written out under its hash, then that hash answered
def post.at(sock: Socket, +at: String, h: String, m: String,
  es: List<&2, Ent>) -> IO(Unit):
  do IO<Unit>:
    a : Bool <- write.all(at, es)
    b : Bool <- write.file(at ++ "/manifest", m)
    post.said(sock, Bool.and(a, b), h)

# a package's manifest and name, computed from its files the way cli_publish
# computes them
def post.write(sock: Socket, dir: String, +es: List<&2, Ent>) -> IO(Unit):
  +m = manifest.of(es)
  +h = hash.of(m)
  post.at(sock, dir ++ "/" ++ h, h, m, es)

# a POST answered: the package it carried, or the reason its body was refused
def post.go(sock: Socket, dir: String, o: Obj) -> IO(Unit):
  match o:
    case OBad{why}:
      answer(sock, "400 Bad Request", why)
    case OOk{items}:
      post.write(sock, dir, sorted(items))

# a POST publishes, anything else fetches
def serve.pick(post: Bool, sock: Socket, dir: String, +path: String,
  body: String) -> IO(Unit):
  match post:
    case True{}:
      post.go(sock, dir, parse(body))
    case False{}:
      get.go(String.eq(path, "/"), sock, dir, path)

# a request's first line taken apart into its method and its path
def serve.req(sock: Socket, dir: String, first: String, body: String) -> IO(Unit):
  +parts = String.split(first, ' ')
  serve.pick(String.eq(S.at(parts, 0n), "POST"), sock, dir, S.at(parts, 1n), body)

# a request served, or refused when its head never ended
def serve.msg(sock: Socket, dir: String, m: S.Msg) -> IO(Unit):
  match m:
    case S.MPartial{}:
      answer(sock, "400 Bad Request", "an incomplete request")
    case S.MFull{head, body}:
      serve.req(sock, dir, S.at(head, 0n), body)

# what a connection read, served
def once.at(got: Socket & String, dir: String) -> IO(Unit):
  (sock, text) = got
  serve.msg(sock, dir, S.msg.of(text))

# one connection, read and answered and shut
def once(sock: Socket, dir: String) -> IO(Unit):
  do IO<Unit>:
    got : Socket & String <- S.request(sock)
    once.at(got, dir)

# a listener with connections left in it, or one that has stopped accepting
type Run is Type:
  RStop{}
  RGo{l: Listener}

# a listener that will not accept is a listener that is finished
def turn.got(r: Result<&1, &1, U32 & String, Socket>, l: Listener, +dir: String,
  rest: String -> Listener -> IO(Run)) -> IO(Run):
  match r:
    case Fail{_e}:
      do IO<Run>:
        Listener.close(l)
        return RStop{}
    case Done{sock}:
      do IO<Run>:
        once(sock, dir)
        rest(dir, l)

# the listener comes back paired with the connection it accepted
def turn.at(got: Listener & Result<&1, &1, U32 & String, Socket>, dir: String,
  rest: String -> Listener -> IO(Run)) -> IO(Run):
  (l, r) = got
  turn.got(r, l, dir, rest)

# a run of connections served one at a time, the listener handed back when the
# run is up so another can have it
def turn(fuel: Nat, dir: String, l: Listener) -> IO(Run):
  match fuel:
    case 0n:
      IO.pure(Run, RGo{l})
    case 1n+f:
      do IO<Run>:
        got : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        turn.at(got, dir, d => lis => turn(f, d, lis))

# a run that ended because the listener did ends the oracle with it
def loop.on(r: Run, dir: String, rest: String -> Listener -> IO(Unit)) -> IO(Unit):
  match r:
    case RStop{}:
      IO.pure(Unit, Unit{})
    case RGo{l}:
      rest(dir, l)

# connections served for as long as the fuel lasts. Bend has no unbounded loop,
# so "forever" is a count no test run will reach: a thousand runs of a thousand
# connections. The count is nested rather than written out because a Nat is
# unary, and the interpreted lane builds the whole of it before it serves
# anything.
def loop(fuel: Nat, +dir: String, l: Listener) -> IO(Unit):
  match fuel:
    case 0n:
      Listener.close(l)
    case 1n+f:
      do IO<Unit>:
        r : Run <- turn(U32.to_nat(1000), dir, l)
        loop.on(r, dir, d => lis => loop(f, d, lis))

# a port that would not open, reported rather than served on
def begin.fail(e: U32 & String) -> IO(Unit):
  (_code, why) = e
  IO.die(Unit, 1, "oracle: cannot listen: " ++ why)

# the listener, once the port is open. The line printed here is the oracle
# saying it is up, though a caller that waits on `GET /` waits on the socket
# itself and not on a pipe it would have to drain.
def begin.at(r: Result<&1, &1, U32 & String, Listener>, +dir: String,
  port: U32) -> IO(Unit):
  match r:
    case Fail{e}:
      begin.fail(e)
    case Done{l}:
      do IO<Unit>:
        IO.print("oracle: " ++ dir ++ " on port " ++ U32.show(port))
        loop(U32.to_nat(1000), dir, l)

# the oracle, on a directory and a port
def begin(dir: String, +port: U32) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Listener> <- TCP.listen(port)
    begin.at(r, dir, port)

# a &1 list copied into a &2 one. `IO.args()` answers a `&1` list, which can be
# read once, and the arguments are read twice here.
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

# the command line: a directory to serve, and a port to serve it on
def start(+as: List<&2, String>) -> IO(Unit):
  begin(S.at(as, 0n), Maybe.default(&2, U32, U32.read(S.at(as, 1n)), 0))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start(copy(xs))
