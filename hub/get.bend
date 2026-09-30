# hub/get: a file fetched from the hub over ezhttp, or read off the disk for a
# `file:` url, and judged by hub/hub against the hash that names it. The GET
# lives apart from the judging because ezhttp reaches foreign code, and bend
# 2.0.32 fails a proof whose imports reach foreign code, so a law may import
# hub/hub but never this.
import Base
import 0xf1c957a470368870a6d1d62a8c0cbe32/main.bend as Http
import 0xf1c957a470368870a6d1d62a8c0cbe32/src/client.bend as Client
import 0xf1c957a470368870a6d1d62a8c0cbe32/src/url.bend as Url
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ../io/file.bend as F
import ./hub.bend as Hub

# what ezhttp answered. It folds a socket that would not open and a reply that
# came apart into one Err, so both are 6.
def get.reply(response: Client.Response) -> String:
  match response:
    case Client.Err{why}:
      "6\n" ++ why
    case Client.Response{+status, _headers, body}:
      Hub.get.status(U32.is_eq(status, 200), status, body)

# a url fetched over a socket
def get.http(url: String) -> IO(String):
  do IO<String>:
    r : Client.Response <- Http.http.get(url)
    return get.reply(r)

# a file url read off the disk
def get.file(+path: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(path)
    return Hub.get.file.got(m, path)

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
  get.loc(Http.parse_url(url), url)

# the file at a url, accepted only when it hashes to `want`
def fetch(+url: String, want: String) -> IO(Hub.Got):
  do IO<Hub.Got>:
    +out : String <- get(url)
    return Hub.judge(R.ok(out), Hub.matches(want, R.text(out)), url, R.text(out))
