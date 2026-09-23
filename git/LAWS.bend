# git: the laws. The human states them; PROOF.bend must prove them.
#
# Vendoring is almost all effect, and an effect proves nothing. The one pure
# decision it makes that anything downstream depends on is the shape of an
# origin table: this module writes it into `.ez/origins.toml`, and
# `lock/lock.bend` reads the same keys back out of a lock's `source` tables. A
# key spelled one way here and another way there produces a lock that
# rebuilds a package from nowhere, and says so no louder than a missing url. That is the law worth stating, and
# until this port it could not be stated at all, because the writer was
# TypeScript and no Bend proof could reach it.
#
# `./git.bend` is spelled `../git/git.bend` here because `lock/lock.bend`
# reaches the same file by that path, and bend gives a file one namespace per
# import closure however many ways it is reached.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../lock/lock.bend as L
import ../git/git.bend as G
import ../pkg/path.bend as P

# LAW: an origin written by this module is read back by the lock as the source
# it was written from. Every key survives, none is shadowed by the pairs that
# follow it, and the tag is whatever those pairs say it is — which is nothing
# at all when the ref asked for was already a commit.
law origin_read:
  for url: String
  for rev: String
  for entry: String
  for root: String
  for nar: String
  for ts: List<&2, T.Kv>
  {L.src_of(G.origin.kvs(url, rev, entry, root, nar, ts))
    == L.Git{url, rev, entry, root, nar, T.value(ts, "tag")} : L.Src}

# The rest of a ref: whether it is already a commit, which table a
# rewrite of origins.toml keeps, and the directory a package is rooted
# at. A tag asked of the remote as if it were a commit fetches nothing,
# and a rewrite that sat a second table behind the first leaves the
# stale origin as the one the lock reads.

# LAW: a ref that is not forty characters is not a commit name. A tag
# or a branch is asked of the remote.
law is_rev_needs_40:
  for +ref: String
  for e: {False{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  {G.is_rev(ref) == False{} : Bool}

# LAW: nor is a name of the right length whose alphabet is not hex.
law is_rev_needs_hex:
  for +ref: String
  for e0: {True{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  for e1: {False{} == G.hex.all(String.to_list(ref)) : Bool}
  {G.is_rev(ref) == False{} : Bool}

# LAW: forty hex characters are a commit name, and need no remote.
law is_rev_hex40:
  for +ref: String
  for e0: {True{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  for e1: {True{} == G.hex.all(String.to_list(ref)) : Bool}
  {G.is_rev(ref) == True{} : Bool}

# LAW: a table of this name is dropped, so vendoring a package again
# replaces what was written for it rather than sitting behind it.
law but_drops:
  for +n: String
  for ps: List<&2, T.Kv>
  for rest: List<&2, T.Sect>
  {G.but(T.Sect{n, ps} <> rest, n) == G.but(rest, n) : List<&2, T.Sect>}

# LAW: a table of another name is kept, in the order it was written.
law but_keeps:
  for +n: String
  for +m: String
  for ps: List<&2, T.Kv>
  for rest: List<&2, T.Sect>
  for e: {False{} == String.eq(n, m) : Bool}
  {G.but(T.Sect{n, ps} <> rest, m)
    == T.Sect{n, ps} <> G.but(rest, m) : List<&2, T.Sect>}

# LAW: when the entry sits at the same depth as the checkout root, the
# recorded root is a climb of nothing off the entry's own directory.
law root_rel_here:
  for +at: String
  for +root: String
  for +entry: String
  for e: {Nat.is_eq(G.depth(P.dir(at)), G.depth(root)) == True{} : Bool}
  {G.root.rel(at, root, entry) == P.climb(0n, P.dir(entry)) : String}

# What `git ls-remote --symref` printed for Giulio2002/bend-sha256. HEAD is
# main, one commit past tag v0.1.0. The parser's job is to find that tip
# and that branch; whether a pin may move is decided in manifest/upgrade.bend.
def sha.remote() -> String:
  "ref: refs/heads/main\tHEAD\n" ++
  "5887e7cefa273ff7f90e3edfd6e90b815bbc79ed\tHEAD\n"

# LAW: the commit row, not the symref row, is the tip
# toward EZ-RES-5
law sha256_remote_tip:
  {G.tip.rev(G.rows(String.lines(sha.remote())))
    == "5887e7cefa273ff7f90e3edfd6e90b815bbc79ed" : String}

# LAW: and the symref row is the branch that tip belongs to
# toward EZ-RES-5
law sha256_remote_branch:
  {G.tip.branch(G.rows(String.lines(sha.remote()))) == "main" : String}

# LAW: when the checkout root is one directory above the entry, the
# recorded root is one climb off the entry's directory.
law root_rel_up:
  for +at: String
  for +root: String
  for +entry: String
  for e: {Nat.is_eq(G.depth(P.dir(at)), 1n+G.depth(root)) == True{} : Bool}
  {G.root.rel(at, root, entry) == P.climb(1n, P.dir(entry)) : String}

# What `ez add` pins. With no ref named, it takes a tag chosen from every tag
# on the remote, and with no semver-ish tag, the branch HEAD's symref names.
# A named ref is looked up by its whole name. Each decision is a pure
# function over what `git ls-remote` printed, and these are its laws.

# LAW: whenever any tag is a release, the tag chosen is a release. No
# pre-release beats one, however much greater its numbers are.
law choose_release:
  for +names: List<&2, String>
  for e: {G.has.release(names) == True{} : Bool}
  {G.release(G.choose(names)) == True{} : Bool}

# LAW: with no release among the tags, the choice is the greatest of them by
# the same comparator, and every semver-ish one of them is a pre-release
law choose_prerelease:
  for +names: List<&2, String>
  for e: {G.has.release(names) == False{} : Bool}
  {G.choose(names) == G.latest(names) : String}

# LAW: the default branch is the one HEAD's symref row names
law branch_of_symref:
  for +b: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.is_empty(b) : Bool}
  {G.tip.branch(G.Row{"ref: refs/heads/" ++ b, "HEAD"} <> rest) == b : String}

# LAW: a row that is not HEAD's says nothing about the default branch
law branch_skips_other:
  for rev: String
  for +name: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.eq(name, "HEAD") : Bool}
  {G.tip.branch(G.Row{rev, name} <> rest) == G.tip.branch(rest) : String}

# LAW: nor does HEAD's commit row, which is not a symref
law branch_skips_commit:
  for +rev: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.starts_with(rev, "ref: ") : Bool}
  {G.tip.branch(G.Row{rev, "HEAD"} <> rest) == G.tip.branch(rest) : String}

# LAW: a row whose ref name is not exactly `refs/tags/<ref>`, its peeled
# `^{}` form, or `refs/heads/<ref>` is never picked: taking it away changes
# nothing. `refs/heads/feature/main` is such a row for `main`.
law exact_skips:
  for rev: String
  for +name: String
  for +rs: List<&2, G.Row>
  for +ref: String
  for e0: {False{} == String.eq(name, "refs/tags/" ++ ref ++ "^{}") : Bool}
  for e1: {False{} == String.eq(name, "refs/tags/" ++ ref) : Bool}
  for e2: {False{} == String.eq(name, "refs/heads/" ++ ref) : Bool}
  {G.exact(G.Row{rev, name} <> rs, ref) == G.exact(rs, ref) : String}

# LAW: a tag the remote has is the answer, whatever branch shares its name
law exact_tag_first:
  for +rs: List<&2, G.Row>
  for +ref: String
  for e: {False{} == String.is_empty(G.named(rs, "refs/tags/" ++ ref)) : Bool}
  {G.exact(rs, ref) == G.or_else(G.named(rs, "refs/tags/" ++ ref ++ "^{}"),
    G.named(rs, "refs/tags/" ++ ref)) : String}

# LAW: a branch is the answer only when no tag of that name is
law exact_branch:
  for +rs: List<&2, G.Row>
  for +ref: String
  for e0: {"" == G.named(rs, "refs/tags/" ++ ref ++ "^{}") : String}
  for e1: {"" == G.named(rs, "refs/tags/" ++ ref) : String}
  {G.exact(rs, ref) == G.named(rs, "refs/heads/" ++ ref) : String}
