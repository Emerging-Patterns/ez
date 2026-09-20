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
# Plaintext only. bend speaks TLS to the real hub, and run/run.bend explains
# why a Bend binary cannot.
import Base

# a string's length where a Nat would be too dear: a body is thousands of
# characters and every one of them would be a Succ
def size(s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{_c, t}:
      U32.inc(size(t))

# the nth of a list of words, or "" when it is not there
def at(xs: List<&2, String>, n: Nat) -> String:
  match xs n:
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
def cut.put(h: String, m: Msg) -> Msg:
  match m:
    case MPartial{}:
      MPartial{}
    case MFull{head, body}:
      MFull{h <> head, body}

# one step of the split, with the answer to "is this the blank line" in hand.
# Under a `Bool.pick` the blank line that ends the head still cost a walk of
# every line of the body, and a `cut.put` rebuilt over each of them.
def cut.step(blank: Bool, t: List<&2, String>, rest: Unit -> Msg) -> Msg:
  match blank:
    case True{}:
      MFull{[], String.join(t, "\n")}
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
def msg.at(m: Msg) -> Msg:
  match m:
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

# whether a request has arrived whole
def complete.of(m: Msg) -> Bool:
  match m:
    case MPartial{}:
      False{}
    case MFull{head, body}:
      U32.is_ge(size(body), clen(head))

# whether what has been read so far is the whole request: its head has ended and
# its body is as long as the head said it would be
def complete(text: String) -> Bool:
  complete.of(msg.of(text))

# an answer's bytes, framed by its length. Every one of them states that length
# and says the connection closes, because bend, curl and nix's fetcher all read
# a body to the length they were promised and then expect the socket to shut.
def response(status: String, +body: String) -> String:
  "HTTP/1.1 " ++ status ++ "\r\nContent-Length: " ++ U32.show(size(body)) ++
    "\r\nConnection: close\r\n\r\n" ++ body

# the socket shut once the answer has gone out
def send.done(sr: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (sock, _r) = sr
  Socket.close(sock)

# one answer written in one go and the connection closed
def answer(sock: Socket, text: String) -> IO(Unit):
  do IO<Unit>:
    sr : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(sock, text)
    send.done(sr)

# the socket handed back once a piece has gone out, so the next one can follow
# it down the same connection
def piece.sent(sr: Socket & Result<&1, &1, U32 & String, Unit>, left: String,
  rest: Socket -> String -> IO(Socket)) -> IO(Socket):
  (sock, _r) = sr
  rest(sock, left)

# nothing left to write is the end of the answer
def piece.more(done: Bool, head: String, tail: String, sock: Socket,
  rest: Socket -> String -> IO(Socket)) -> IO(Socket):
  match done:
    case True{}:
      IO.pure(Socket, sock)
    case False{}:
      do IO<Socket>:
        sr : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(sock, head)
        piece.sent(sr, tail, rest)

# an answer written out a few characters at a time, one write per piece, so a
# client meets a header or a chunk length that straddles two of its reads. That
# is the case a framing client breaks on, and a server that hands its whole
# answer over in one write never presents it.
def piece.go(fuel: Nat, +n: Nat, sock: Socket, +text: String) -> IO(Socket):
  match fuel:
    case 0n:
      IO.pure(Socket, sock)
    case 1n+f:
      piece.more(String.is_empty(text), String.take(text, n),
        String.drop(text, n), sock, s => t => piece.go(f, n, s, t))

# one answer written in pieces of n characters and the connection closed. The
# fuel is one piece per character, which no answer can outrun.
def pieces(sock: Socket, n: Nat, +text: String) -> IO(Unit):
  do IO<Unit>:
    sock2 : Socket <- piece.go(String.length(text), n, sock, text)
    Socket.close(sock2)

# an empty chunk means the client stopped writing, whole request or not
def recv.chunk(chunk: String, sock: Socket, acc: String,
  rest: Socket -> String -> IO(Socket & String)) -> IO(Socket & String):
  match chunk:
    case SNil{}:
      IO.pure(Socket & String, (sock, acc))
    case SCon{c, t}:
      rest(sock, acc ++ SCon{c, t})

# a failed read ends the request as surely as an empty one
def recv.got(r: Result<&1, &1, U32 & String, String>, sock: Socket, acc: String,
  rest: Socket -> String -> IO(Socket & String)) -> IO(Socket & String):
  match r:
    case Fail{_e}:
      IO.pure(Socket & String, (sock, acc))
    case Done{chunk}:
      recv.chunk(chunk, sock, acc, rest)

# the socket comes back paired with what it read
def recv.next(got: Socket & Result<&1, &1, U32 & String, String>, acc: String,
  rest: Socket -> String -> IO(Socket & String)) -> IO(Socket & String):
  (sock, r) = got
  recv.got(r, sock, acc, rest)

# nothing more is asked for once the whole request is in hand
def recv.more(done: Bool, sock: Socket, acc: String,
  rest: Socket -> String -> IO(Socket & String)) -> IO(Socket & String):
  match done:
    case True{}:
      IO.pure(Socket & String, (sock, acc))
    case False{}:
      do IO<Socket & String>:
        got : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(sock, 65536)
        recv.next(got, acc, rest)

# a whole request read off a socket, one chunk at a time until the head has
# ended and the body is as long as Content-Length promised
def recv.go(fuel: Nat, sock: Socket, +acc: String) -> IO(Socket & String):
  match fuel:
    case 0n:
      IO.pure(Socket & String, (sock, acc))
    case 1n+f:
      recv.more(complete(acc), sock, acc, s => a => recv.go(f, s, a))

# a whole request read off a socket, and the socket it came on
def request(sock: Socket) -> IO(Socket & String):
  recv.go(U32.to_nat(4096), sock, "")
