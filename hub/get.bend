# hub/get: a file fetched from the hub. The answer is a status on its own
# first line and then the text, the shape a run answers with. ezhttp's client
# speaks the socket. Its main.bend also imports the server, and TCP.listen
# there still takes a port alone, which Bend 2.0.32 rejects, so this imports
# the client and the url parser on their own.
import Base
import 0x5e4e2a9db839a0214ace6923b04b685b/client.bend as Client
import 0x5e4e2a9db839a0214ace6923b04b685b/url.bend as Url
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ../io/file.bend as F
import ./hub.bend as Hub

# a status other than 200 is a miss with the number in it, never a body
def get.status(ok: Bool, status: U32, body: String) -> String:
  match ok:
    case True{}:
      "0\n" ++ body
    case False{}:
      "22\nthe server answered " ++ U32.show(status)

# what ezhttp answered. It folds a socket that would not open and a reply that
# came apart into one Err, so both are 6.
def get.reply(response: Client.Response) -> String:
  match response:
    case Client.Err{why}:
      "6\n" ++ why
    case Client.Response{+status, _headers, body}:
      get.status(U32.is_eq(status, 200), status, body)

# a url fetched over a socket
def get.http(url: String) -> IO(String):
  do IO<String>:
    r : Client.Response <- Client.client.get(url, [])
    return get.reply(r)

# a file url read off the disk. curl served these too, and a test that wants a
# body without a server to serve it is the reason to keep them.
def get.file.got(got: Maybe<&2, String>, path: String) -> String:
  match got:
    case None{}:
      "2\n" ++ path ++ " is not there"
    case Some{s}:
      "0\n" ++ s

# a file url read off the disk
def get.file(+path: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(path)
    return get.file.got(m, path)

# a url whose scheme decides where the body comes from
def get.scheme(file: Bool, url: String, path: String) -> IO(String):
  match file:
    case True{}:
      get.file(path)
    case False{}:
      get.http(url)

# a url that came apart, or the reason it did not
def get.loc(loc: Url.Loc, url: String) -> IO(String):
  match loc:
    case Url.Bad{why}:
      IO.pure(String, "22\n" ++ why)
    case Url.Loc{+scheme, _host, _port, path}:
      get.scheme(String.eq(scheme, "file"), url, path)

# the body at a url: "0" and the body, or a status and the reason
def get(+url: String) -> IO(String):
  get.loc(Url.parse(url), url)

# the file at a url, accepted only when it hashes to `want`
def fetch(+url: String, want: String) -> IO(Hub.Got):
  do IO<Hub.Got>:
    +out : String <- get(url)
    return Hub.judge(R.ok(out), Hub.matches(want, R.text(out)), url, R.text(out))

