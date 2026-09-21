# git: the laws. The human states them; PROOF.bend must prove them.
#
# Vendoring is almost all effect, and an effect proves nothing. The one pure
# decision it makes that anything downstream depends on is the shape of
# `.ez/origins.toml`: this module writes it and `lock/lock.bend` reads it, and
# nothing else in ez ever sees the file. A key spelled one way here and
# another way there produces a lock that rebuilds a package from nowhere, and
# says so no louder than a missing url. That is the law worth stating, and
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

# The shapes git/git.bend had before this pass rewrote them for cost, kept
# here so the rewrites' risk can be stated rather than sampled, the way
# net/LAWS.bend keeps the shapes net/http.bend had before its dechunk
# rewrite. Nothing but the laws below reads them.
#
# What was wrong with them is not what they answer, it is what they cost.
# `Bool.pick`, `Bool.and` and `Bool.or` are ordinary functions: every arm and
# both sides are reduced before the answer is chosen, so a search written with
# them never stops at what it found. That matters here because `is_rev` is
# asked of every ref ez resolves, and `peeled` of every row `ls-remote` wrote.

# the alphabet scan, before
def old.among(+c: Char, cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +h <> t:
      Bool.or(Char.is_eq(h, c), old.among(c, t))

# the ref walk, before
def old.hex.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      Bool.and(G.hex.at(h), old.hex.all(t))

# the peeled-row search, before
def old.peeled(rs: List<&2, G.Row>) -> String:
  match rs:
    case []:
      ""
    case +h <> t:
      Bool.pick(String, G.row.peeled(h), G.row.rev(h), old.peeled(t))

# LAW: the alphabet scan that stops at the char it found answers what the scan
# that read past it answered
law among_agrees:
  for +c: Char
  for cs: List<&2, Char>
  {old.among(c, cs) == G.among(c, cs) : Bool}

# LAW: and the ref walk that stops at the first char a commit name may not
# hold answers what the walk that did not stop answered
law hex_all_agrees:
  for cs: List<&2, Char>
  {old.hex.all(cs) == G.hex.all(cs) : Bool}

# LAW: and the search that stops at the first peeled row answers what the
# search that walked every row answered. This is the one that decides which
# commit a tag pins, so a rewrite of it is a rewrite of what gets locked.
law peeled_agrees:
  for rs: List<&2, G.Row>
  {old.peeled(rs) == G.peeled(rs) : String}

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
law sha256_remote_tip:
  {G.tip.rev(G.rows(String.lines(sha.remote())))
    == "5887e7cefa273ff7f90e3edfd6e90b815bbc79ed" : String}

# LAW: and the symref row is the branch that tip belongs to
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
