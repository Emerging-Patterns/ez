# hub/hub: a file fetched from the hub, and checked against the hash that names
# it. bend accepts any prefix of the sha256, and a package's `0x` name is the
# first 32 characters of its manifest's digest, so the check is a prefix test.
import Base
import 0x0a372da4a053652f70ded7d6e0d19330/main.bend as Http
import 0x0a372da4a053652f70ded7d6e0d19330/client.bend as Client
import 0x0a372da4a053652f70ded7d6e0d19330/url.bend as Url
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as File
import ../sha/sha.bend as Sha

# The GET is ezhttp's. What is kept here is the answer's shape: a status on
# its own first line and then the text, the shape a run answers with and the
# one curl's answer had, so `R.ok` and `R.text` read it.

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
    r : Client.Response <- Http.http.get(url)
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
    m : Maybe<&2, String> <- File.read(path)
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
  get.loc(Http.parse_url(url), url)

# a body is the one that was asked for when its digest starts with the hash
def matches(want: String, +body: String) -> Bool:
  String.starts_with(Sha.hex(body), want)

# what a fetch answered: the body when it arrived and hashed right, otherwise
# the reason, so a caller never mistakes an error page for a package file
type Got is Data:
  Miss{why: String}
  Have{body: String}

# the digest's verdict on a body that did arrive
def judge.hash(good: Bool, url: String, body: String) -> Got:
  match good:
    case True{}:
      Have{body}
    case False{}:
      Miss{url ++ " does not hash to what was asked for"}

# a fetch judged, once the run and the digest are both known
def judge(ok: Bool, good: Bool, url: String, body: String) -> Got:
  match ok:
    case False{}:
      Miss{url ++ ": " ++ body}
    case True{}:
      judge.hash(good, url, body)

# the file at a url, accepted only when it hashes to `want`
def fetch(+url: String, want: String) -> IO(Got):
  do IO<Got>:
    +out : String <- get(url)
    return judge(R.ok(out), matches(want, R.text(out)), url, R.text(out))

# a fetch's outcome on one line
def show(got: Got) -> String:
  match got:
    case Miss{why}:
      "miss " ++ why
    case Have{body}:
      "have " ++ body
