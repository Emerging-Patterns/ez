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
# EZ-RES-1
law is_rev_needs_40:
  for +ref: String
  for e: {False{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  {G.is_rev(ref) == False{} : Bool}

# LAW: nor is a name of the right length whose alphabet is not hex.
# EZ-RES-1
law is_rev_needs_hex:
  for +ref: String
  for e0: {True{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  for e1: {False{} == G.hex.all(String.to_list(ref)) : Bool}
  {G.is_rev(ref) == False{} : Bool}

# LAW: forty hex characters are a commit name, and need no remote.
# EZ-RES-1
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
# EZ-RES-1
law choose_release:
  for +names: List<&2, String>
  for e: {G.has.release(names) == True{} : Bool}
  {G.release(G.choose(names)) == True{} : Bool}

# LAW: with no release among the tags, the choice is the greatest of them by
# the same comparator, and every semver-ish one of them is a pre-release
# EZ-RES-1
law choose_prerelease:
  for +names: List<&2, String>
  for e: {G.has.release(names) == False{} : Bool}
  {G.choose(names) == G.latest(names) : String}

# LAW: the default branch is the one HEAD's symref row names
# EZ-RES-1
law branch_of_symref:
  for +b: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.is_empty(b) : Bool}
  {G.tip.branch(G.Row{"ref: refs/heads/" ++ b, "HEAD"} <> rest) == b : String}

# LAW: a row that is not HEAD's says nothing about the default branch
# EZ-RES-1
law branch_skips_other:
  for rev: String
  for +name: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.eq(name, "HEAD") : Bool}
  {G.tip.branch(G.Row{rev, name} <> rest) == G.tip.branch(rest) : String}

# LAW: nor does HEAD's commit row, which is not a symref
# EZ-RES-1
law branch_skips_commit:
  for +rev: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.starts_with(rev, "ref: ") : Bool}
  {G.tip.branch(G.Row{rev, "HEAD"} <> rest) == G.tip.branch(rest) : String}

# LAW: a row whose ref name is not exactly `refs/tags/<ref>`, its peeled
# `^{}` form, or `refs/heads/<ref>` is never picked: taking it away changes
# nothing. `refs/heads/feature/main` is such a row for `main`.
# EZ-RES-1
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
# EZ-RES-1
law exact_tag_first:
  for +rs: List<&2, G.Row>
  for +ref: String
  for e: {False{} == String.is_empty(G.named(rs, "refs/tags/" ++ ref)) : Bool}
  {G.exact(rs, ref) == G.or_else(G.named(rs, "refs/tags/" ++ ref ++ "^{}"),
    G.named(rs, "refs/tags/" ++ ref)) : String}

# LAW: a branch is the answer only when no tag of that name is
# EZ-RES-1
law exact_branch:
  for +rs: List<&2, G.Row>
  for +ref: String
  for e0: {"" == G.named(rs, "refs/tags/" ++ ref ++ "^{}") : String}
  for e1: {"" == G.named(rs, "refs/tags/" ++ ref) : String}
  {G.exact(rs, ref) == G.named(rs, "refs/heads/" ++ ref) : String}

# Which tag is greatest. Each law takes the tags as any list with one tag `n`
# somewhere in it, `xs ++ [n] ++ ys`, so it speaks of every tag in every list.
# "Greater" is `G.newer` of `G.ord.ver`, the comparator the folds use: numeric
# parts compare as numbers, missing parts pad with zero, and a pre-release
# compares by semver's rules below the release it precedes.

# LAW: no semver-ish tag is newer than the one `latest` answers
# EZ-RES-1
law latest_greatest:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +ns: List<&2, Nat>
  for +ps: List<&2, G.Id>
  for +ev: {G.ver.of(n) == G.Yes{ns, ps} : G.Ver}
  {G.newer(G.ord.ver(G.ver.of(n),
    G.ver.of(G.latest(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: no release is newer than the one `latest.rel` answers
# EZ-RES-1
law latest_rel_greatest:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +e: {G.release(n) == True{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n),
    G.ver.of(G.latest.rel(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: the tag `ez add` pins is the greatest release: no release on the
# remote is newer, and with `choose_release` it is itself a release
# EZ-RES-1
law choose_greatest_release:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +e: {G.release(n) == True{} : Bool}
  {G.newer(G.ord.ver(G.ver.of(n),
    G.ver.of(G.choose(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: with no release on the remote, the tag `ez add` pins is the greatest
# pre-release: no semver-ish tag is newer
# EZ-RES-1
law choose_greatest_prerelease:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +ns: List<&2, Nat>
  for +ps: List<&2, G.Id>
  for +ev: {G.ver.of(n) == G.Yes{ns, ps} : G.Ver}
  for +e: {G.has.release(List.append(&2, String, xs, n <> ys)) == False{}
    : Bool}
  {G.newer(G.ord.ver(G.ver.of(n),
    G.ver.of(G.choose(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: and the tag it pins, when it pins one, is one of the remote's tags
# EZ-RES-1
law choose_is_a_tag:
  for +names: List<&2, String>
  for e: {String.is_empty(G.choose(names)) == False{} : Bool}
  exs xs: List<&2, String>
  exs ys: List<&2, String>
  {List.append(&2, String, xs, G.choose(names) <> ys) == names
    : List<&2, String>}

# The default branch tip `ez lock --upgrade` moves a pin by its commit alone
# to is `tip.rev` of what `ls-remote --symref <url> HEAD` printed: the commit
# on HEAD's own row, and not the symref row above it.

# LAW: the tip is the commit HEAD's commit row names
# EZ-RES-5
law tip_of_head:
  for +rev: String
  for rest: List<&2, G.Row>
  for e: {True{} == G.is_rev(rev) : Bool}
  {G.tip.rev(G.Row{rev, "HEAD"} <> rest) == rev : String}

# LAW: a row that is not HEAD's names no tip
# EZ-RES-5
law tip_skips_other:
  for +rev: String
  for +name: String
  for rest: List<&2, G.Row>
  for e: {False{} == String.eq(name, "HEAD") : Bool}
  {G.tip.rev(G.Row{rev, name} <> rest) == G.tip.rev(rest) : String}

# LAW: nor does HEAD's symref row, whose first field is not a commit
# EZ-RES-5
law tip_skips_symref:
  for +rev: String
  for rest: List<&2, G.Row>
  for e: {False{} == G.is_rev(rev) : Bool}
  {G.tip.rev(G.Row{rev, "HEAD"} <> rest) == G.tip.rev(rest) : String}
