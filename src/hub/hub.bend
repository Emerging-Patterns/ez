# hub/hub: a file fetched from the hub, and checked against the hash that names
# it. bend accepts any prefix of the sha256, and a package's `0x` name is the
# first 32 characters of its manifest's digest, so the check is a prefix test.
import Base
import ../share/sha.bend as Sha

# The GET is ezhttp's, run by hub/get. What is kept here is the answer's shape: a status on
# its own first line and then the text, the shape a run answers with and the
# one curl's answer had, so `R.ok` and `R.text` read it.

# a status other than 200 is a miss with the number in it, never a body
def get.status(ok: Bool, status: U32, body: String) -> String:
  match ok:
    case True{}:
      "0\n" ++ body
    case False{}:
      "22\nthe server answered " ++ U32.show(status)

# a file url read off the disk. curl served these too, and a test that wants a
# body without a server to serve it is the reason to keep them.
def get.file.got(got: Maybe<&2, String>, path: String) -> String:
  match got:
    case None{}:
      "2\n" ++ path ++ " is not there"
    case Some{s}:
      "0\n" ++ s

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

# a fetch's outcome on one line
def show(got: Got) -> String:
  match got:
    case Miss{why}:
      "miss " ++ why
    case Have{body}:
      "have " ++ body
