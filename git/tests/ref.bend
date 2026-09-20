# git: what a ref resolves to, and what an origin is written as. The effects
# are exercised end to end by `tests/git.bend`; these are the decisions made
# before any program is run, which no end-to-end test can pin down on its own.
import Base
import ../git.bend as G
import ../../manifest/toml.bend as T
import ../../check/kit.bend as Check

# what `git ls-remote` prints for an annotated tag: the tag object, and then
# the commit it points at, the second row peeled
def annotated() -> List<&2, String>:
  ["1111111111111111111111111111111111111111\trefs/tags/v1.0",
    "2222222222222222222222222222222222222222\trefs/tags/v1.0^{}"]

# what it prints for a branch, which has no peeled form at all
def branch() -> List<&2, String>:
  ["3333333333333333333333333333333333333333\trefs/heads/main"]

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a commit name needs no remote asked about it",
      Bool.pick(String,
        G.is_rev("2222222222222222222222222222222222222222"), "yes", "no"),
      "yes")
    Check.eq_str("a tag is not a commit name",
      Bool.pick(String, G.is_rev("v1.0"), "yes", "no"), "no")
    Check.eq_str("nor is a name of the right length that is not hex",
      Bool.pick(String,
        G.is_rev("222222222222222222222222222222222222222z"), "yes", "no"),
      "no")
    Check.eq_str("an annotated tag resolves through its peeled row",
      G.pick(G.rows(annotated())),
      "2222222222222222222222222222222222222222")
    Check.eq_str("a branch resolves through the only row there is",
      G.pick(G.rows(branch())),
      "3333333333333333333333333333333333333333")
    Check.eq_str("a ref the remote does not have resolves to nothing",
      G.pick(G.rows([])), "")
    Check.eq_str("an origin is a table named after the package hash",
      T.render([G.origin("0xaa", "https://h/r", "c0ffee", "src/lib.bend",
        "src", "sha256-x", "v1.0")]),
      "[origins.\"0xaa\"]\nkind = \"git\"\nurl = \"https://h/r\"\n" ++
      "rev = \"c0ffee\"\nentry = \"src/lib.bend\"\nroot = \"src\"\n" ++
      "narHash = \"sha256-x\"\ntag = \"v1.0\"\n")
    Check.eq_str("a ref that was already a commit leaves no tag behind",
      T.render([G.origin("0xaa", "https://h/r", "c0ffee", "lib.bend", ".",
        "sha256-x", "")]),
      "[origins.\"0xaa\"]\nkind = \"git\"\nurl = \"https://h/r\"\n" ++
      "rev = \"c0ffee\"\nentry = \"lib.bend\"\nroot = \".\"\n" ++
      "narHash = \"sha256-x\"\n")
    Check.eq_str("vendoring a package again replaces what it said before",
      G.origins.text("[origins.\"0xbb\"]\nkind = \"git\"\nurl = \"o\"\n" ++
        "[origins.\"0xaa\"]\nkind = \"git\"\nurl = \"old\"\n",
        G.origin("0xaa", "new", "c0ffee", "lib.bend", ".", "sha256-x", "")),
      "[origins.\"0xbb\"]\nkind = \"git\"\nurl = \"o\"\n\n" ++
      "[origins.\"0xaa\"]\nkind = \"git\"\nurl = \"new\"\n" ++
      "rev = \"c0ffee\"\nentry = \"lib.bend\"\nroot = \".\"\n" ++
      "narHash = \"sha256-x\"\n")
    Check.eq_str("a package rooted at the entry's own directory says so",
      G.root.rel("/w/.work-c0ffee/src/lib.bend", "/w/.work-c0ffee/src",
        "src/lib.bend"), "src")
    Check.eq_str("a package rooted at the repo itself says so too",
      G.root.rel("/w/.work-c0ffee/lib.bend", "/w/.work-c0ffee", "lib.bend"),
      ".")
    Check.eq_str("a module reached through `..` re-roots a directory up",
      G.root.rel("/w/.work-c0ffee/a/b/lib.bend", "/w/.work-c0ffee/a",
        "a/b/lib.bend"), "a")
    Check.eq_str("and one that climbs past the repo says that too",
      G.root.rel("/w/.work-c0ffee/lib.bend", "/w", "lib.bend"), "..")

#|ok a commit name needs no remote asked about it
#|ok a tag is not a commit name
#|ok nor is a name of the right length that is not hex
#|ok an annotated tag resolves through its peeled row
#|ok a branch resolves through the only row there is
#|ok a ref the remote does not have resolves to nothing
#|ok an origin is a table named after the package hash
#|ok a ref that was already a commit leaves no tag behind
#|ok vendoring a package again replaces what it said before
#|ok a package rooted at the entry's own directory says so
#|ok a package rooted at the repo itself says so too
#|ok a module reached through `..` re-roots a directory up
#|ok and one that climbs past the repo says that too
