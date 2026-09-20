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
import ../manifest/toml.bend as T
import ../lock/lock.bend as L
import ../git/git.bend as G

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
