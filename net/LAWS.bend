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

# LAW: a body shorter than the Content-Length it was framed with is
# torn, so a cut connection is not a short file.
law clen_short:
  for st: U32
  for +n: Nat
  for +body: String
  for e: {True{} == Nat.is_lt(Http.utf8.len(body), n) : Bool}
  {Http.parse.clen(st, n, body)
    == Http.Torn{"the response body stopped before its Content-Length"}
    : Http.Reply}

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

# LAW: a chunked body decodes the same however the reads fell. The
# bytes taken and dropped at any offset are the same bytes, so the
# decode of the join is the decode of the whole.
law dechunk_split:
  for +s: String
  for +n: Nat
  {Http.dechunk(s)
    == Http.dechunk(String.append(Http.utf8.take(s, n), Http.utf8.drop(s, n)))
    : String}

# The rest of the text: what ez writes to a server, and how it cuts up what a
# server writes back. A parser that reads the wrong field out of a line is
# wrong the same way a miscounted body is wrong, so the cuts are stated too.

# whether a string holds a character nowhere. This is the vocabulary the laws
# about the split need and nothing else uses: a chunk header with no extension
# marker, a status line's first word with no space in it.
def avoids(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(Char.is_eq(h, c)), avoids(t, c))

# LAW: a string that holds the character nowhere splits into itself, one
# piece. The two laws below are read off this one and the one under it.
law split_whole:
  for +s: String
  for +c: Char
  for +e: {avoids(s, c) == True{} : Bool}
  {String.split(s, c) == [s] : List<&2, String>}

# LAW: and a string that holds it first at a known place splits there, with
# everything before the character as the first piece and the rest split on
# after it. This is what "the first occurrence" means, stated so a proof can
# use it.
law split_cut:
  for +s: String
  for +c: Char
  for +r: String
  for +e: {avoids(s, c) == True{} : Bool}
  {String.split(String.append(s, SCon{c, r}), c) == s <> String.split(r, c)
    : List<&2, String>}

# LAW: a chunk header's extension does not change the length it states. This
# is the claim `hexlen` is written on -- anything after a `;` is an extension
# -- and it is the one that decides how much of the stream is body, so a
# framer that read the extension as part of the number would cut the body in
# the wrong place.
law hexlen_ignores_extension:
  for +s: String
  for ext: String
  for +e: {avoids(s, ';') == True{} : Bool}
  {Http.hexlen(String.append(s, SCon{';', ext})) == Http.hexlen(s) : Nat}

# LAW: the first piece of a line split on a space is the word before the
# space.
law first_is_first_word:
  for +w: String
  for r: String
  for +e: {avoids(w, ' ') == True{} : Bool}
  {Http.first(String.split(String.append(w, SCon{' ', r}), ' ')) == w : String}

# LAW: and the second piece is the first word of what follows the space. This
# is how the status code is read off `HTTP/1.1 200 OK`: `second` is not a
# second scan of the line but the first of what was left, so a version string
# holding a space could not shift the field ez reads.
law second_is_next_word:
  for +w: String
  for r: String
  for +e: {avoids(w, ' ') == True{} : Bool}
  {Http.second(String.split(String.append(w, SCon{' ', r}), ' '))
    == Http.first(String.split(r, ' ')) : String}

# LAW: the request line asks for the path it was given, whole. A request that
# truncated or escaped the path would fetch a different package under the
# right name, which is the one failure the hub cannot catch for us.
law request_names_path:
  for +host: String
  for +path: String
  {String.starts_with(Http.request(host, path), "GET " ++ path) == True{}
    : Bool}

# LAW: a response whose head never ended is torn, and no body is read out of
# it. `Connection: close` makes the end of the connection the end of the body,
# so a connection that dropped mid-head must not look like a short reply.
law parse_needs_blank_line:
  for +raw: String
  for e: {Http.NoCut{} == Http.divide(raw, "\r\n\r\n") : Http.Cut}
  {Http.parse(raw) == Http.Torn{"the response head has no blank line after it"}
    : Http.Reply}

# LAW: and when the head did end, the body is everything after the blank line
# and the head is everything before it, with the blank line in neither.
law parse_splits_at_blank_line:
  for +raw: String
  for before: String
  for after: String
  for e: {Http.Cut{before, after} == Http.divide(raw, "\r\n\r\n") : Http.Cut}
  {Http.parse(raw) == Http.parse.head(String.lines(before), after)
    : Http.Reply}

# LAW: with neither framing header the rest of the connection is the
# body, whole. `Connection: close` asked for that frame, and a body
# that was cut to nothing would be a different file.
law unframed_is_rest:
  for st: U32
  for body: String
  {Http.parse.len(st, None{}, body) == Http.Reply{st, body} : Http.Reply}

# LAW: a header is found after the line is cased down, so the case
# the server wrote it in does not hide it. The name is asked for in
# lower case.
law head_hit_ignores_case:
  for +h: String
  for +name: String
  {Http.head.hit(h, name)
    == String.starts_with(String.to_lower(h), name ++ ":") : Bool}

# LAW: a head whose first line holds no status code is torn, and the
# body after it is not read as a reply.
law parse_needs_status:
  for +ls: List<&2, String>
  for body: String
  for e: {None{} == U32.read(Http.second(String.split(Http.first(ls), ' ')))
    : Maybe<&2, U32>}
  {Http.parse.head(ls, body)
    == Http.Torn{"the response has no status line"}
    : Http.Reply}

# LAW: a torn response says so before it says anything else, so a test reading
# `show` cannot mistake the reason for a body.
law show_torn_is_marked:
  for why: String
  {String.starts_with(Http.show(Http.Torn{why}), "torn ") == True{} : Bool}

# LAW: and a reply opens with the status it holds, whole.
law show_reply_opens_with_status:
  for +status: U32
  for body: String
  {String.starts_with(Http.show(Http.Reply{status, body}), U32.show(status))
    == True{} : Bool}

# LAW: only https implies 443. Every other scheme gets 80, and nothing else is
# guessed at: a scheme ez does not know is not a scheme ez invents a port for.
law dflt_plain:
  for +scheme: String
  for e: {False{} == String.eq(scheme, "https") : Bool}
  {Url.dflt(scheme) == 80 : U32}

# LAW: https implies 443. This is the one scheme that is not the
# plain port, so a url that named no port still reaches the server
# on the port TLS listens on.
law dflt_https:
  {Url.dflt("https") == 443 : U32}

# LAW: the scheme is everything before the first colon, cased down, and the
# colons after it survive, because the rest is joined back up before it is
# read. A port, or a colon anywhere in the path, is therefore not a second
# scheme.
law parse_scheme_first:
  for +url: String
  for h: String
  for t: List<&2, String>
  for e: {h <> t == String.split(url, ':') : List<&2, String>}
  {Url.parse(url) == Url.parse.rest(String.to_lower(h), String.join(t, ":"))
    : Url.Loc}

# LAW: a file url with an empty authority has no host and the
# plain port. The empty authority is not a host ez invents one
# for, and the scheme is not https, so the port is 80 and the
# path is the path.
law file_empty_host:
  for path: String
  {Url.parse.auth("file", [""], path)
    == Url.Loc{"file", "", 80, path} : Url.Loc}

# LAW: a url whose rest does not open with `//` is refused, and
# the reason names the url as it was written. A scheme with no
# slashes is not a host and a path; it is this error.
law parse_needs_slashes:
  for +scheme: String
  for +rest: String
  for e: {False{} == String.starts_with(rest, "//") : Bool}
  {Url.parse.rest(scheme, rest)
    == Url.Bad{scheme ++ ":" ++ rest ++ " has no //"}
    : Url.Loc}

# LAW: a url that would not come apart says so before it says anything else
law url_show_bad_is_marked:
  for why: String
  {String.starts_with(Url.show(Url.Bad{why}), "bad ") == True{} : Bool}

# LAW: and one that did come apart opens with the scheme it came apart into
law url_show_opens_with_scheme:
  for +scheme: String
  for host: String
  for port: U32
  for path: String
  {String.starts_with(Url.show(Url.Loc{scheme, host, port, path}), scheme)
    == True{} : Bool}
