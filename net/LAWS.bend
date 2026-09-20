# net: the laws. The human states them; PROOF.bend must prove them. A body
# framed by a byte count is the one place in ez where a miscount is silent:
# the bytes still decode, they are just the wrong bytes. So the framing is
# proved rather than sampled.
import Base
import ./http.bend as Http
import ./url.bend as Url

# LAW: the path a url comes apart into is always absolute, however few or many
# slashes the url had. The request line is `GET <path> HTTP/1.1`, so a path
# that did not start at the root would be a request no server answers.
law path_absolute:
  for ps: List<&2, String>
  {String.starts_with(Url.path.of(ps), "/") == True{} : Bool}

# LAW: take and drop partition a string at the same byte offset, whatever the
# offset and whatever the string holds. Nothing is lost between them and
# nothing is counted twice.
law utf8_split:
  for s: String
  for +n: Nat
  {String.append(Http.utf8.take(s, n), Http.utf8.drop(s, n)) == s : String}

# LAW: a body whose Content-Length is its own byte count comes back exactly,
# with nothing cut off its end and nothing left on it. This is the claim the
# whole client rests on: a framed body is the body.
law clen_exact:
  for st: U32
  for +body: String
  {Http.parse.clen(st, Http.utf8.len(body), body) == Http.Reply{st, body} : Http.Reply}

# The shapes net/http.bend had before the dechunk rewrite, kept here so that
# the rewrite's one real risk can be stated rather than sampled: that the fast
# definitions answer exactly what the slow ones answered, on every input.
# These are the specification; net/http.bend is the implementation. Nothing
# but the laws below reads them, and a reader who wants to know what the
# rewrite changed can read them against http.bend side by side.
#
# What was wrong with them is not what they answer, it is what they cost. Each
# recursive call sits in an arm of a `Bool.pick`, which is an ordinary
# function and so builds both of its arms before it picks one; and the chunk
# loop appends onto an accumulator, which copies every chunk decoded so far.

# the take, before
def old.take(s: String, +n: Nat) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      +w = Http.utf8.width(Char.to_u32(h))
      Bool.pick(String, Nat.is_lt(n, w), SNil{},
        SCon{h, old.take(t, Nat.sub(n, w))})

# the drop, before
def old.drop(s: String, +n: Nat) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      +w = Http.utf8.width(Char.to_u32(h))
      Bool.pick(String, Nat.is_lt(n, w), SCon{h, t},
        old.drop(t, Nat.sub(n, w)))

# the walk under divide, before
def old.divide.go(s: String, +pat: String, +n: Nat) -> Http.Cut:
  match s:
    case SNil{}:
      Http.NoCut{}
    case SCon{+h, +t}:
      Bool.pick(Http.Cut, String.starts_with(SCon{h, t}, pat),
        Http.Cut{"", String.drop(SCon{h, t}, n)},
        Http.divide.push(h, old.divide.go(t, pat, n)))

# the divide, before
def old.divide(s: String, +pat: String) -> Http.Cut:
  old.divide.go(s, pat, String.length(pat))

# the hex read, before
def old.hex.go(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+h, t}:
      +v = Http.hex.val(h)
      Bool.pick(Nat, U32.is_ge(v, 16), acc,
        old.hex.go(t, Nat.add(Nat.mul(acc, 16n), U32.to_nat(v))))

# the chunk loop, before: the accumulator that made the decode quadratic
def old.chunks(fuel: Nat, c: Http.Cut, acc: String) -> String:
  match fuel c:
    case 0n _:
      acc
    case 1n+f Http.NoCut{}:
      acc
    case 1n+f Http.Cut{before, +after}:
      +n = Http.hexlen(before)
      old.chunks(f,
        Http.divide(Http.utf8.drop(after, Nat.add(n, 2n)), "\r\n"),
        acc ++ Http.utf8.take(after, n))

# the dechunk, before
def old.dechunk(+s: String) -> String:
  old.chunks(String.length(s), Http.divide(s, "\r\n"), "")

# LAW: the take that stops takes what the take that did not stop took. This
# and the three laws under it are the whole risk of the dechunk rewrite: a
# faster definition is only a fix if it is the same definition.
law take_agrees:
  for s: String
  for +n: Nat
  {old.take(s, n) == Http.utf8.take(s, n) : String}

# LAW: and the same for the drop
law drop_agrees:
  for s: String
  for +n: Nat
  {old.drop(s, n) == Http.utf8.drop(s, n) : String}

# LAW: and for the walk that now really does stop at the first hit
law divide_agrees:
  for s: String
  for +pat: String
  {old.divide(s, pat) == Http.divide(s, pat) : Http.Cut}

# LAW: and for the hex read that now really does stop at the first non-digit
law hex_agrees:
  for s: String
  for +acc: Nat
  {old.hex.go(s, acc) == Http.hex.go(s, acc) : Nat}

# LAW: a chunked body decodes to what it decoded to before the accumulator
# came out of the loop. This is the quadratic fix itself, and it is the one
# rewrite that changed the loop rather than one step of it.
law dechunk_agrees:
  for +s: String
  {old.dechunk(s) == Http.dechunk(s) : String}
