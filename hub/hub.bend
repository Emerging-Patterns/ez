# hub/hub: a file checked against the hash that names it. bend accepts any
# prefix of the sha256, and a package's `0x` name is the first 32 characters
# of its manifest's digest, so the check is a prefix test. The fetch itself
# is hub/get.bend.
import Base
import ../share/sha.bend as Sha

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
