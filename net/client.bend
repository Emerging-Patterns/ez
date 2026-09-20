# net/client: a url fetched. The parsing in net/url.bend and net/http.bend
# joined to the socket in net/wire.bend, and nothing more: ez asks for one
# thing, the body of a GET, and this answers that.
#
# The answer is shaped the way run/run.bend shapes one, a status on its own
# first line and then the text, so `R.ok` and `R.text` read it and hub/hub.bend
# keeps the contract it had when curl gave the same two lines.
import Base
import ./url.bend as Url
import ./http.bend as Http
import ./wire.bend as Wire
import ../io/file.bend as File
import ../run/run.bend as R

# a status other than 200 is a miss with the number in it, never a body
def get.status(ok: Bool, status: U32, body: String) -> IO(String):
  match ok:
    case True{}:
      IO.pure(String, "0\n" ++ body)
    case False{}:
      IO.pure(String, "22\nthe server answered " ++ U32.show(status))

# what a parsed response amounts to
def get.body(r: Http.Reply) -> IO(String):
  match r:
    case Http.Torn{why}:
      IO.pure(String, "5\n" ++ why)
    case Http.Reply{+status, body}:
      get.status(U32.is_eq(status, 200), status, body)

# a finished exchange. A failed one already answers with its own status and
# reason, so it passes straight through.
def get.done(raw: String, ok: Bool) -> IO(String):
  match ok:
    case False{}:
      IO.pure(String, raw)
    case True{}:
      get.body(Http.parse(R.text(raw)))

# a url fetched over a socket
def get.http(secure: Bool, +host: String, port: U32, path: String) -> IO(String):
  do IO<String>:
    +raw : String <- Wire.talk(secure, host, port, Http.request(host, path))
    get.done(raw, R.ok(raw))

# a file url read off the disk. curl served these too, and a test that wants a
# body without a server to serve it is the reason to keep them.
def get.file.got(m: Maybe<&2, String>, path: String) -> IO(String):
  match m:
    case None{}:
      IO.pure(String, "2\n" ++ path ++ " is not there")
    case Some{s}:
      IO.pure(String, "0\n" ++ s)

# a file url read off the disk
def get.file(+path: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- File.read(path)
    get.file.got(m, path)

# a url whose scheme decides where the body comes from
def get.scheme(file: Bool, secure: Bool, host: String, port: U32,
  path: String) -> IO(String):
  match file:
    case True{}:
      get.file(path)
    case False{}:
      get.http(secure, host, port, path)

# a url that came apart, or the reason it did not
def get.loc(l: Url.Loc) -> IO(String):
  match l:
    case Url.Bad{why}:
      IO.pure(String, "22\n" ++ why)
    case Url.Loc{+scheme, host, port, path}:
      get.scheme(String.eq(scheme, "file"), String.eq(scheme, "https"),
        host, port, path)

# the body at a url: "0" and the body, or a status and the reason
def get(url: String) -> IO(String):
  get.loc(Url.parse(url))
