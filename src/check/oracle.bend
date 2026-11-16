# check/oracle: a local stand-in for the package hub, so `bend --publish` can be
# run without touching hub.bend-lang.com. It accepts the POST, computes the
# package hash the way cli_publish does, writes the package out, and answers
# with that hash, which is what bend checks the response against. Anything that
# is not a POST is a file served out of the same directory, so a published
# package can be fetched back.
#
#   bend check/oracle.bend <dir> <port>
#
# What is here is the hub's sockets and writing. The reading of a body is pure
# and is check/body.bend, where a law can reach it without the sockets.
# Reading a request off a socket and writing an answer back are check/serve.bend,
# shared with check/framing.bend. Plaintext HTTP only; bend speaks TLS to the
# real hub, and check/serve.bend says why a Bend binary cannot.
#
# `GET /` answers `ok`, so a script can wait for the oracle before it publishes,
# and `GET /pow.json` the least proof-of-work difficulty bend accepts.
# One connection is served at a time, each answer states its length and closes
# the socket, and the oracle stops of its own accord after a million of them.
import Base
import ../io/file.bend as F
import snap@1.6.0.0/main.bend as R
import ./serve.bend as S
import ./body.bend as B
import ./argv.bend as Argv

# one answer written and the connection closed. Every answer states its length
# and says the connection closes, because bend, curl and nix's fetcher all read
# a body to the length they were promised and then expect the socket to shut.
def answer(sock: Socket, status: String, body: String) -> IO(Unit):  # noqa: L001 IO: test server socket write
  S.answer(sock, S.response(status, body))

# a file that was there, or the 404 for one that was not
def serve.file(sock: Socket, got: Maybe<&2, String>) -> IO(Unit):
  match got:
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

# `/pow.json` is the difficulty bend mines a proof of work against before it
# uploads (`{"files": .., "nonce": N}`). The oracle asks for the least, 1, so
# the first nonce bend tries passes, and it takes the nonce it is sent unchecked.
def get.pow(pow: Bool, sock: Socket, dir: String, +path: String) -> IO(Unit):
  match pow:
    case True{}:
      answer(sock, "200 OK", "{\"pow\": 1}")
    case False{}:
      get.go(String.eq(path, "/"), sock, dir, path)

# a file written once its directory exists
def write.after(out: String, at: String, text: String) -> IO(Bool):
  do IO<Bool>:
    ok : Bool <- F.write(at, text)
    return Bool.and(R.ok(out), ok)

# one file written, with its parent directories made first. Base has no mkdir,
# so a program is run for it.
def write.file(+at: String, text: String) -> IO(Bool):
  do IO<Bool>:
    out : String <- R.exec(["mkdir", "-p", B.parent.of(at)])
    write.after(out, at, text)

# one file of a package written under the package's directory
def write.ent(dir: String, entry: B.Ent) -> IO(Bool):
  B.Ent{p, t} = entry
  write.file(dir ++ "/" ++ p, t)

# every file of a package written
def write.all(+dir: String, es: List<&2, B.Ent>) -> IO(Bool):
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
def post.said(sock: Socket, ok: Bool, digest: String) -> IO(Unit):
  match ok:
    case True{}:
      answer(sock, "200 OK", digest)
    case False{}:
      answer(sock, "500 Internal Server Error", "the package could not be written")

# the package written out under its hash, then that hash answered
def post.at(sock: Socket, +at: String, digest: String, listing: String, es: List<&2, B.Ent>) -> IO(Unit):
  do IO<Unit>:
    a : Bool <- write.all(at, es)
    b : Bool <- write.file(at ++ "/manifest", listing)
    post.said(sock, Bool.and(a, b), digest)

# a package's manifest and name, computed from its files the way cli_publish
# computes them
def post.write(sock: Socket, dir: String, +es: List<&2, B.Ent>) -> IO(Unit):
  +m = B.manifest.of(es)
  +h = B.hash.of(m)
  post.at(sock, dir ++ "/" ++ h, h, m, es)

# a POST answered: the package it carried, or the reason its body was refused
def post.go(sock: Socket, dir: String, parsed: B.Obj) -> IO(Unit):
  match parsed:
    case B.OBad{why}:
      answer(sock, "400 Bad Request", why)
    case B.OOk{items}:
      post.write(sock, dir, B.sorted(items))

# a POST publishes, anything else fetches
def serve.pick(post: Bool, sock: Socket, dir: String, +path: String, body: String) -> IO(Unit):
  match post:
    case True{}:
      post.go(sock, dir, B.parse(body))
    case False{}:
      get.pow(String.eq(path, "/pow.json"), sock, dir, path)

# a request's first line taken apart into its method and its path
def serve.req(sock: Socket, dir: String, first: String, body: String) -> IO(Unit):
  +parts = String.split(first, ' ')
  serve.pick(String.eq(S.at(parts, 0n), "POST"), sock, dir, S.at(parts, 1n), body)

# a request served, or refused when its head never ended
def serve.msg(sock: Socket, dir: String, msg: S.Msg) -> IO(Unit):
  match msg:
    case S.MPartial{}:
      answer(sock, "400 Bad Request", "an incomplete request")
    case S.MFull{head, body}:
      serve.req(sock, dir, S.at(head, 0n), body)

# what a connection read, served
def once.at(got: Socket & String, dir: String) -> IO(Unit):
  (sock, text) = got
  serve.msg(sock, dir, S.msg.of(text))

# one connection, read and answered and shut
def once(sock: Socket, dir: String) -> IO(Unit):  # noqa: L001 IO: test server connection
  do IO<Unit>:
    got : Socket & String <- S.request(sock)
    once.at(got, dir)

# a listener with connections left in it, or one that has stopped accepting
type Run is Type:  # noqa: L001 holds a Listener, which no law reaches
  RStop{}
  RGo{l: Listener}

# a listener that will not accept is a listener that is finished
def turn.got(
  accepted: Result<&1, &1, U32 & String, Socket>,
  listener: Listener,
  +dir: String,
  rest: String -> Listener -> IO(Run)
) -> IO(Run):
  match accepted:
    case Fail{_e}:
      do IO<Run>:
        Listener.close(listener)
        return RStop{}
    case Done{sock}:
      do IO<Run>:
        once(sock, dir)
        rest(dir, listener)

# the listener comes back paired with the connection it accepted
def turn.at(
  got: Listener & Result<&1, &1, U32 & String, Socket>,
  dir: String,
  rest: String -> Listener -> IO(Run)
) -> IO(Run):
  (l, r) = got
  turn.got(r, l, dir, rest)

# a run of connections served one at a time, the listener handed back when the
# run is up so another can have it
def turn(fuel: Nat, dir: String, listener: Listener) -> IO(Run):  # noqa: L001 IO: test server accept loop
  match fuel:
    case 0n:
      IO.pure(Run, RGo{listener})
    case 1n+f:
      do IO<Run>:
        got : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(listener)
        turn.at(got, dir, d => lis => turn(f, d, lis))

# a run that ended because the listener did ends the oracle with it
def loop.on(state: Run, dir: String, rest: String -> Listener -> IO(Unit)) -> IO(Unit):
  match state:
    case RStop{}:
      IO.pure(Unit, Unit{})
    case RGo{l}:
      rest(dir, l)

# a thousand: the runs the server takes, and the connections each run serves.
# Bend has no unbounded loop, so "forever" is a count no test run will reach, a
# thousand runs of a thousand connections; a server has no input to size it by.
def thousand() -> Nat:  # noqa: L001 fuel for the accept loop, an IO driver
  1000n

# connections served for as long as the fuel lasts. Bend has no unbounded loop,
# so "forever" is a count no test run will reach: a thousand runs of a thousand
# connections. The count is nested rather than written out because a Nat is
# unary, and the interpreted lane builds the whole of it before it serves
# anything.
def loop(fuel: Nat, +dir: String, listener: Listener) -> IO(Unit):  # noqa: L001 IO: test server accept loop
  match fuel:
    case 0n:
      Listener.close(listener)
    case 1n+f:
      do IO<Unit>:
        r : Run <- turn(thousand(), dir, listener)
        loop.on(r, dir, d => lis => loop(f, d, lis))

# a port that would not open, reported rather than served on
def begin.fail(err: U32 & String) -> IO(Unit):
  (_code, why) = err
  IO.die(Unit, 1, "oracle: cannot listen: " ++ why)

# the listener, once the port is open. The line printed here is the oracle
# saying it is up, though a caller that waits on `GET /` waits on the socket
# itself and not on a pipe it would have to drain.
def begin.at(bound: Result<&1, &1, U32 & String, Listener>, +dir: String, port: U32) -> IO(Unit):
  match bound:
    case Fail{e}:
      begin.fail(e)
    case Done{l}:
      do IO<Unit>:
        IO.print("oracle: " ++ dir ++ " on port " ++ U32.show(port))
        loop(thousand(), dir, l)

# the oracle, on a directory and a port
def begin(dir: String, +port: U32) -> IO(Unit):  # noqa: L001 IO: test server listen
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Listener> <- TCP.listen("127.0.0.1", port)
    begin.at(r, dir, port)

# the command line: a directory to serve, and a port to serve it on
def start(+as: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver: the command line
  begin(S.at(as, 0n), Maybe.default(&2, U32, U32.read(S.at(as, 1n)), 0))

def main() -> IO(Unit):  # noqa: L001 IO entry point
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start(Argv.args(xs))
