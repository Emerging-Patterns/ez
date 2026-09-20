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
