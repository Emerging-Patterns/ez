# check/serve: the plaintext HTTP a test server has to speak before it can be
# about anything. Reading a request off a socket until it has all arrived, and
# writing an answer back, are the same work whether the server stands in for
# the package hub (check/oracle.bend) or for a server that frames a body two
# ways (check/framing.bend), so they are here and those two are only what they
# are about.
#
# Nothing here opens a port or accepts a connection: an accept loop has to hold
# whatever the server answers with, and a Bend value threaded through a loop is
# threaded by hand. Each server writes its own loop over `recv` and `send`.
#
# Plaintext only. bend speaks TLS to the real hub. A Bend binary cannot serve
# it: `bend -o` links no -lssl, so ezhttp's client reaches OpenSSL only by
# opening it at run time, and Base's TCP has no crypto at all.
import Base

# how many bytes a character takes in UTF-8, which is how the socket carries it
def width(+code: U32) -> U32:
  Bool.pick(U32, U32.is_lt(code, 128), 1,
    Bool.pick(U32, U32.is_lt(code, 2048), 2,
      Bool.pick(U32, U32.is_lt(code, 65536), 3, 4)))

# a string's length in the bytes it goes over the wire as, which is what a
# Content-Length or a chunk size counts, held in a U32 where a Nat would be too
# dear: a body is thousands of characters and every one of them would be a
# Succ. A character is not a byte: `bend --publish` sends a non-ASCII source
# as it is, and counting characters would wait forever for the rest.
def size(text: String) -> U32:
  match text:
    case SNil{}:
      0
    case SCon{c, t}:
      U32.add(width(Char.to_u32(c)), size(t))

# the nth of a list of words, or "" when it is not there
def at(xs: List<&2, String>, index: Nat) -> String:
  match xs index:
    case Nil{} _m:
      ""
    case Con{h, _t} 0n:
      h
    case Con{_h, t} 1n+p:
      at(t, p)

# a request read off a socket: its head lines and its body, or a request whose
# head has not arrived in full yet
type Msg is Data:
  MPartial{}
  MFull{head: List<&2, String>, body: String}

# a head line put back in front of the ones after it
def cut.put(line: String, message: Msg) -> Msg:
  match message:
    case MPartial{}:
      MPartial{}
    case MFull{head, body}:
      MFull{line <> head, body}

# one step of the split, with the answer to "is this the blank line" in hand.
# Under a `Bool.pick` the blank line that ends the head still cost a walk of
# every line of the body, and a `cut.put` rebuilt over each of them.
def cut.step(blank: Bool, lines: List<&2, String>, rest: Unit -> Msg) -> Msg:
  match blank:
    case True{}:
      MFull{[], String.join(lines, "\n")}
    case False{}:
      rest(Unit{})

# a request's lines split at the blank one. The body is joined back with the
# newlines it was split on, so nothing in it is lost or invented.
def cut(ls: List<&2, String>) -> Msg:
  match ls:
    case []:
      MPartial{}
    case +h <> +t:
      cut.step(Bool.or(String.is_empty(h), String.eq(h, "\r")), t,
        _u => cut.put(h, cut(t)))

# a request whose head came out empty has not arrived: nothing has been read
# yet, and the one blank line that split it was the whole of it
def msg.head(hs: List<&2, String>, body: String) -> Msg:
  match hs:
    case []:
      MPartial{}
    case h <> t:
      MFull{h <> t, body}

# a split that found no head at all, taken back
def msg.at(message: Msg) -> Msg:
  match message:
    case MPartial{}:
      MPartial{}
    case MFull{head, body}:
      msg.head(head, body)

# what has been read off a socket so far, as a request
def msg.of(text: String) -> Msg:
  msg.at(cut(String.lines(text)))

# a head line's Content-Length, or whatever the lines after it stated
def clen.at(+line: String, rest: U32) -> U32:
  Bool.pick(U32, String.starts_with(String.to_lower(line), "content-length:"),
    Maybe.default(&2, U32, U32.read(String.trim(String.drop(line, 15n))), 0),
    rest)

# how long a head says its body is, or zero when it says nothing
def clen(hs: List<&2, String>) -> U32:
  match hs:
    case []:
      0
    case h <> t:
      clen.at(h, clen(t))

# an answer's bytes, framed by its length. Every one of them states that length
# and says the connection closes, because bend, curl and nix's fetcher all read
# a body to the length they were promised and then expect the socket to shut.
def response(status: String, +body: String) -> String:
  "HTTP/1.1 " ++ status ++ "\r\nContent-Length: " ++ U32.show(size(body)) ++
    "\r\nConnection: close\r\n\r\n" ++ body

# the socket shut once the answer has gone out
def send.done(sr: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (sock, _r) = sr
  Socket.close(sock)

# one answer written in one go and the connection closed
def answer(sock: Socket, text: String) -> IO(Unit):  # noqa: L001 IO: test server socket write
  do IO<Unit>:
    sr : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send(sock, text)
    send.done(sr)

# the socket handed back once a piece has gone out, so the next one can follow
# it down the same connection
def piece.sent(
  sr: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>,
  left: String,
  rest: Socket -> String -> IO(Socket)
) -> IO(Socket):
  (sock, _r) = sr
  rest(sock, left)

# nothing left to write is the end of the answer
def piece.more(
  done: Bool,
  head: String,
  tail: String,
  sock: Socket,
  rest: Socket -> String -> IO(Socket)
) -> IO(Socket):
  match done:
    case True{}:
      IO.pure(Socket, sock)
    case False{}:
      do IO<Socket>:
        sr : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send(sock, head)
        piece.sent(sr, tail, rest)

# an answer written out a few characters at a time, one write per piece, so a
# client meets a header or a chunk length that straddles two of its reads. That
# is the case a framing client breaks on, and a server that hands its whole
# answer over in one write never presents it.
def piece.go(fuel: Nat, +width: Nat, sock: Socket, +text: String) -> IO(Socket):
  match fuel:
    case 0n:
      IO.pure(Socket, sock)
    case 1n+f:
      piece.more(String.is_empty(text), String.take(text, width),
        String.drop(text, width), sock, s => t => piece.go(f, width, s, t))

# one answer written in pieces of n characters and the connection closed. The
# fuel is one piece per character, which no answer can outrun.
def pieces(sock: Socket, width: Nat, +text: String) -> IO(Unit):  # noqa: L001 IO: test server socket write
  do IO<Unit>:
    sock2 : Socket <- piece.go(String.length(text), width, sock, text)
    Socket.close(sock2)

# what has been read so far, the chunks newest first, put back in order
def recv.text(parts: List<&2, String>) -> String:
  String.concat(List.reverse(&2, String, parts))

# an empty chunk means the client stopped writing, whole request or not
def recv.chunk(text: String) -> Maybe<&1, String>:
  match text:
    case SNil{}:
      None{}
    case SCon{c, t}:
      Some{SCon{c, t}}

# what one read gave: a chunk, or None when the peer is done sending, the
# read failed or the chunk was empty, all of which end the request
def recv.got(received: Result<&1, &1, U32 & String, Maybe<&1, String>>) -> Maybe<&1, String>:
  match received:
    case Fail{_e}:
      None{}
    case Done{chunk}:
      Maybe.bind(&1, String, String, chunk, recv.chunk)

# the socket comes back paired with what it read
def recv.one.of(
  got: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>
) -> IO(Socket & Maybe<&1, String>):
  (sock, r) = got
  IO.pure(Socket & Maybe<&1, String>, (sock, recv.got(r)))

# one read off the socket, and the socket back
def recv.one(sock: Socket) -> IO(Socket & Maybe<&1, String>):
  do IO<Socket & Maybe<&1, String>>:
    got : Socket & Result<&1, &1, U32 & String, Maybe<&1, String>> <- TCP.recv(sock, 65536)
    recv.one.of(got)

# a chunk taken into the parts and the walk gone on, or the request as it
# stands once the reads have ended
def recv.then(
  read: Socket & Maybe<&1, String>,
  parts: List<&2, String>,
  rest: Socket -> String -> List<&2, String> -> IO(Socket & String)
) -> IO(Socket & String):
  (sock, chunk) = read
  match chunk:
    case None{}:
      IO.pure(Socket & String, (sock, recv.text(parts)))
    case Some{+text}:
      rest(sock, text, text <> parts)

# a request that is whole is done; one that is not reads one more chunk and
# goes on with it
def recv.more(
  done: Bool,
  sock: Socket,
  parts: List<&2, String>,
  rest: Socket -> String -> List<&2, String> -> IO(Socket & String)
) -> IO(Socket & String):
  match done:
    case True{}:
      IO.pure(Socket & String, (sock, recv.text(parts)))
    case False{}:
      do IO<Socket & String>:
        read : Socket & Maybe<&1, String> <- recv.one(sock)
        recv.then(read, parts, rest)

# the body, once the head is settled: each chunk is counted as it comes, so
# the request is put together once, when the body is as long as `need`
def recv.body(
  fuel: Nat,
  sock: Socket,
  parts: List<&2, String>,
  +have: U32,
  +need: U32
) -> IO(Socket & String):
  match fuel:
    case 0n:
      IO.pure(Socket & String, (sock, recv.text(parts)))
    case 1n+f:
      recv.more(U32.is_ge(have, need), sock, parts,
        s => c => ps => recv.body(f, s, ps, U32.add(have, size(c)), need))

# a head that has ended. While nothing of the body has come, the next chunk
# may still move where the head ends, so the head is looked at again. Once a
# byte of the body has come, the head is settled and every later chunk is
# body, so the body goes on by count.
def recv.head.full(
  empty: Bool,
  +have: U32,
  +need: U32,
  fuel: Nat,
  sock: Socket,
  parts: List<&2, String>,
  again: Socket -> String -> List<&2, String> -> IO(Socket & String)
) -> IO(Socket & String):
  match empty:
    case True{}:
      recv.more(U32.is_ge(have, need), sock, parts, again)
    case False{}:
      recv.more(U32.is_ge(have, need), sock, parts,
        s => c => ps => recv.body(fuel, s, ps, U32.add(have, size(c)), need))

# the head not yet whole: one more chunk read. Whole: on to the body
def recv.head.at(
  message: Msg,
  fuel: Nat,
  sock: Socket,
  parts: List<&2, String>,
  again: Socket -> String -> List<&2, String> -> IO(Socket & String)
) -> IO(Socket & String):
  match message:
    case MPartial{}:
      recv.more(False{}, sock, parts, again)
    case MFull{head, +body}:
      recv.head.full(String.is_empty(body), size(body), clen(head), fuel, sock, parts, again)

# a whole request read off a socket, one chunk at a time until the head has
# ended and the body is as long as Content-Length promised
def recv.head(fuel: Nat, sock: Socket, +parts: List<&2, String>) -> IO(Socket & String):
  match fuel:
    case 0n:
      IO.pure(Socket & String, (sock, recv.text(parts)))
    case 1n+(+f):
      recv.head.at(msg.of(recv.text(parts)), f, sock, parts, s => _c => ps => recv.head(f, s, ps))

# the reads a request may take, 64 KiB at most each: 256 MiB, past any request
# a test sends. How long a request is is not known until its head has arrived,
# so the reads cannot be counted up front.
def reads() -> Nat:  # noqa: L001 fuel for the request read loop, an IO driver
  4096n

# a whole request read off a socket, and the socket it came on
def request(sock: Socket) -> IO(Socket & String):  # noqa: L001 IO: test server socket read
  recv.head(reads(), sock, [])
