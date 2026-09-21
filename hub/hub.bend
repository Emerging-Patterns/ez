# hub/hub: a file fetched from the hub, and checked against the hash that names
# it. bend accepts any prefix of the sha256, and a package's `0x` name is the
# first 32 characters of its manifest's digest, so the check is a prefix test.
import Base
import ../net/client.bend as Client
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../sha/sha.bend as Sha

# the body of a GET, from ez's own client (net/client.bend). The answer keeps
# the shape a run answers with, a status on its own first line and then the
# text, which is the shape curl's answer had.
def get(url: String) -> IO(String):
  Client.get(url)

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
def show(g: Got) -> String:
  match g:
    case Miss{why}:
      "miss " ++ why
    case Have{body}:
      "have " ++ body
