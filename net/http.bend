# net/http: the text of HTTP/1.1, and nothing that touches a socket. A GET
# request is formatted here and a response is taken apart here, so what a
# reply means can be stated without a server to say it.
import Base

# a string divided at the first occurrence of a pattern, or not divided at all
type Cut is Data:
  NoCut{}
  Cut{before: String, after: String}

# what a response turned out to be: a status and a framed body, or the reason
# the bytes were not a response
type Reply is Data:
  Torn{why: String}
  Reply{status: U32, body: String}

# the first of a list of pieces, "" when there are none
def first(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case h <> t:
      h

# the second of a list of pieces, "" when there is no second
def second(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case h <> t:
      first(t)

# one char of the divide, put back on the front of what the rest found
def divide.push(h: Char, r: Cut) -> Cut:
  match r:
    case NoCut{}:
      NoCut{}
    case Cut{before, after}:
      Cut{SCon{h, before}, after}

# the walk: the pattern is looked for here, and only when it is not here does
# the rest of the string get looked at, so a hit near the front stops near the
# front
def divide.go(s: String, +pat: String, +n: Nat) -> Cut:
  match s:
    case SNil{}:
      NoCut{}
    case SCon{+h, +t}:
      Bool.pick(Cut, String.starts_with(SCon{h, t}, pat),
        Cut{"", String.drop(SCon{h, t}, n)},
        divide.push(h, divide.go(t, pat, n)))

# a string in two halves, around the first occurrence of a pattern. The pattern
# itself belongs to neither half.
def divide(s: String, +pat: String) -> Cut:
  divide.go(s, pat, String.length(pat))

# the value of one hex digit's code point, or 16 when it is not one
def hex.of(+u: U32) -> U32:
  Bool.pick(U32, Bool.and(U32.is_ge(u, 48), U32.is_le(u, 57)), U32.sub(u, 48),
    Bool.pick(U32, Bool.and(U32.is_ge(u, 97), U32.is_le(u, 102)), U32.sub(u, 87),
      Bool.pick(U32, Bool.and(U32.is_ge(u, 65), U32.is_le(u, 70)), U32.sub(u, 55),
        16)))

# the value of one hex digit, or 16 when the char is not one
def hex.val(c: Char) -> U32:
  hex.of(Char.to_u32(c))

# the hex digits at the front of a string, read until one is not a digit
def hex.go(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+h, t}:
      +v = hex.val(h)
      Bool.pick(Nat, U32.is_ge(v, 16), acc,
        hex.go(t, Nat.add(Nat.mul(acc, 16n), U32.to_nat(v))))

# the length a chunk header states. Anything after a `;` is an extension, and
# no extension ez could meet changes the length.
def hexlen(s: String) -> Nat:
  hex.go(String.trim(first(String.split(s, ';'))), 0n)

# a chunked body put back together. One pass: a chunk header has been divided
# off, its length says how much of what follows is body, and the rest is the
# next header. A zero length leaves nothing to divide, so the next pass ends.
# The fuel is the body's own length, which no chunk walk can outlast.
def chunks(fuel: Nat, c: Cut, acc: String) -> String:
  match fuel c:
    case 0n _:
      acc
    case 1n+f NoCut{}:
      acc
    case 1n+f Cut{before, +after}:
      +n = hexlen(before)
      chunks(f, divide(String.drop(after, Nat.add(n, 2n)), "\r\n"),
        acc ++ String.take(after, n))

# a `Transfer-Encoding: chunked` body as the bytes it stands for
def dechunk(+s: String) -> String:
  chunks(String.length(s), divide(s, "\r\n"), "")

# whether a head line names this header. The name is given in lower case; a
# server may write it any way it likes.
def head.hit(h: String, +name: String) -> Bool:
  String.starts_with(String.to_lower(h), name ++ ":")

# this line's value when it is the header asked for, otherwise what the lines
# after it answered, so the first one written wins
def head.pick(hit: Bool, h: String, name: String, rest: String) -> String:
  match hit:
    case True{}:
      String.trim(String.drop(h, Nat.add(String.length(name), 1n)))
    case False{}:
      rest

# the value a head gave a header, "" when it gave none
def head.go(ls: List<&2, String>, +name: String) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      head.pick(head.hit(h, name), h, name, head.go(t, name))

# the request line and the headers of a GET. `Connection: close` is what makes
# the end of the connection the end of the body, which is the only framing
# every server agrees on.
def request(host: String, path: String) -> String:
  "GET " ++ path ++ " HTTP/1.1\r\n"
    ++ "Host: " ++ host ++ "\r\n"
    ++ "User-Agent: ez\r\n"
    ++ "Accept: */*\r\n"
    ++ "Connection: close\r\n\r\n"

# a body against the length its head promised: a body shorter than that is a
# connection that dropped, not a short file
def parse.short(status: U32, n: Nat, body: String, short: Bool) -> Reply:
  match short:
    case True{}:
      Torn{"the response body stopped before its Content-Length"}
    case False{}:
      Reply{status, String.take(body, n)}

# a body framed by Content-Length
def parse.clen(status: U32, +n: Nat, +body: String) -> Reply:
  parse.short(status, n, body, Nat.is_lt(String.length(body), n))

# a body framed by Content-Length when there was one. With neither header the
# end of the connection framed it, which `Connection: close` asked for.
def parse.len(status: U32, m: Maybe<&2, Nat>, body: String) -> Reply:
  match m:
    case None{}:
      Reply{status, body}
    case Some{n}:
      parse.clen(status, n, body)

# a body framed the way its head said to frame it
def parse.pick(status: U32, chunked: Bool, len: String, body: String) -> Reply:
  match chunked:
    case True{}:
      Reply{status, dechunk(body)}
    case False{}:
      parse.len(status, Nat.read(len), body)

# the two headers that decide the framing, read off the head
def parse.frame(status: U32, te: String, len: String, body: String) -> Reply:
  parse.pick(status, String.contains(String.to_lower(te), "chunked"), len, body)

# a head whose status line has been read
def parse.status(m: Maybe<&2, U32>, +ls: List<&2, String>, body: String) -> Reply:
  match m:
    case None{}:
      Torn{"the response has no status line"}
    case Some{n}:
      parse.frame(n, head.go(ls, "transfer-encoding"),
        head.go(ls, "content-length"), body)

# the head's lines, with the status line read off the first
def parse.head(+ls: List<&2, String>, body: String) -> Reply:
  parse.status(U32.read(second(String.split(first(ls), ' '))), ls, body)

# a response divided into its head and everything after the blank line
def parse.cut(c: Cut) -> Reply:
  match c:
    case NoCut{}:
      Torn{"the response head has no blank line after it"}
    case Cut{before, after}:
      parse.head(String.lines(before), after)

# the status and the body of a raw response
def parse(raw: String) -> Reply:
  parse.cut(divide(raw, "\r\n\r\n"))

# a parsed response on one line, for a test to read
def show(r: Reply) -> String:
  match r:
    case Torn{why}:
      "torn " ++ why
    case Reply{status, body}:
      U32.show(status) ++ " " ++ body
