# check/framing: a plaintext server whose whole subject is how a response is
# framed. It answers one body by Content-Length, one in chunks, and anything
# else with a status and no body, which is the three cases net/http.bend has to
# get right; tests/fetch.bend starts one of these and drives ez's own client
# against it.
#
#   bend check/framing.bend <port>
#
# Every answer goes out seven characters at a time, one write per piece, so a
# chunk length or a header lands across two of the client's reads. A client
# that only works when the whole answer arrives in one read works against no
# real server, and a test server that writes in one go never says so.
#
# The HTTP itself is check/serve.bend, shared with check/oracle.bend. What is
# here is the routes, the chunking, and the accept loop that holds them.
import Base
import ./serve.bend as S

# the body framed by its length
def plain() -> String:
  "a manifest line\n"

# the pieces the chunked body is framed in, which are deliberately words rather
# than lines: a client that puts them back together wrongly says so in its
# spacing
def chunks() -> List<&2, String>:
  ["one ", "two ", "three ", "four\n"]

# the hex digits, in order, so a digit is an index rather than arithmetic on a
# character
def digits() -> List<&2, String>:
  ["0", "1", "2", "3", "4", "5", "6", "7",
   "8", "9", "a", "b", "c", "d", "e", "f"]

# one hex digit
def hex.digit(x: U32) -> String:
  S.at(digits(), U32.to_nat(x))

# a length as a chunk header states it. The chunks here are a handful of
# characters each, so two digits covers every length this server can produce.
def hex.show(+x: U32) -> String:
  Bool.pick(String, U32.is_lt(x, 16), hex.digit(x),
    hex.digit(U32.div(x, 16)) ++ hex.digit(U32.mod(x, 16)))

# one chunk: its length in hex, then its bytes, each ended by a CRLF
def chunk(+s: String) -> String:
  hex.show(S.size(s)) ++ "\r\n" ++ s ++ "\r\n"

# the chunks of a body, one after another
def chunked.go(ss: List<&2, String>) -> String:
  match ss:
    case []:
      "0\r\n\r\n"
    case h <> t:
      chunk(h) ++ chunked.go(t)

# a body framed in chunks rather than by a length, headers and all
def chunked() -> String:
  "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n" ++
    chunked.go(chunks())

# what a path is answered with. `/` answers so a caller can wait for the server
# on the socket itself rather than on a pipe it would have to drain, and every
# other unknown path is a status with no body at all.
def reply(+path: String) -> String:
  Bool.pick(String, String.eq(path, "/plain"), S.response("200 OK", plain()),
    Bool.pick(String, String.eq(path, "/chunked"), chunked(),
      Bool.pick(String, String.eq(path, "/"), S.response("200 OK", "ok"),
        S.response("404 Not Found", ""))))

# a request's first line taken apart, and its path answered
def serve.req(sock: Socket, first: String) -> IO(Unit):
  S.pieces(sock, 7n, reply(S.at(String.split(first, ' '), 1n)))

# a request served, or refused when its head never ended
def serve.msg(sock: Socket, m: S.Msg) -> IO(Unit):
  match m:
    case S.MPartial{}:
      S.answer(sock, S.response("400 Bad Request", "an incomplete request"))
    case S.MFull{head, _body}:
      serve.req(sock, S.at(head, 0n))

# what a connection read, served
def once.at(got: Socket & String) -> IO(Unit):
  (sock, text) = got
  serve.msg(sock, S.msg.of(text))

# one connection, read and answered and shut
def once(sock: Socket) -> IO(Unit):
  do IO<Unit>:
    got : Socket & String <- S.request(sock)
    once.at(got)

# a listener with connections left in it, or one that has stopped accepting
type Run is Type:
  RStop{}
  RGo{l: Listener}

# a listener that will not accept is a listener that is finished
def turn.got(r: Result<&1, &1, U32 & String, Socket>, l: Listener,
  rest: Listener -> IO(Run)) -> IO(Run):
  match r:
    case Fail{_e}:
      do IO<Run>:
        Listener.close(l)
        return RStop{}
    case Done{sock}:
      do IO<Run>:
        once(sock)
        rest(l)

# the listener comes back paired with the connection it accepted
def turn.at(got: Listener & Result<&1, &1, U32 & String, Socket>,
  rest: Listener -> IO(Run)) -> IO(Run):
  (l, r) = got
  turn.got(r, l, rest)

# a run of connections served one at a time, the listener handed back when the
# run is up so another can have it
def turn(fuel: Nat, l: Listener) -> IO(Run):
  match fuel:
    case 0n:
      IO.pure(Run, RGo{l})
    case 1n+f:
      do IO<Run>:
        got : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        turn.at(got, lis => turn(f, lis))

# a run that ended because the listener did ends the server with it
def loop.on(r: Run, rest: Listener -> IO(Unit)) -> IO(Unit):
  match r:
    case RStop{}:
      IO.pure(Unit, Unit{})
    case RGo{l}:
      rest(l)

# connections served for as long as the fuel lasts. Bend has no unbounded loop,
# so "forever" is a count no test run will reach: a thousand runs of a thousand
# connections. The count is nested rather than written out because a Nat is
# unary, and the interpreted lane builds the whole of it before it serves
# anything.
def loop(fuel: Nat, l: Listener) -> IO(Unit):
  match fuel:
    case 0n:
      Listener.close(l)
    case 1n+f:
      do IO<Unit>:
        r : Run <- turn(U32.to_nat(1000), l)
        loop.on(r, lis => loop(f, lis))

# a port that would not open, reported rather than served on
def begin.fail(e: U32 & String) -> IO(Unit):
  (_code, why) = e
  IO.die(Unit, 1, "framing: cannot listen: " ++ why)

# the listener, once the port is open
def begin.at(r: Result<&1, &1, U32 & String, Listener>, port: U32) -> IO(Unit):
  match r:
    case Fail{e}:
      begin.fail(e)
    case Done{l}:
      do IO<Unit>:
        IO.print("framing: on port " ++ U32.show(port))
        loop(U32.to_nat(1000), l)

# the server, on a port
def begin(+port: U32) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Listener> <- TCP.listen(port)
    begin.at(r, port)

# a &1 list copied into a &2 one. `IO.args()` answers a `&1` list, which can be
# read once, and the argument is read twice here.
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

# the command line: a port to serve on
def start(as: List<&2, String>) -> IO(Unit):
  begin(Maybe.default(&2, U32, U32.read(S.at(as, 0n)), 0))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start(copy(xs))
