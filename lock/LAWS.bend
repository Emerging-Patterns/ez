# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L

# LAW: a package resolves to the origin recorded for it, whatever origins
# follow. A second record of the same hash never shadows the first, so
# `.ez/origins.toml` is read the way it was written.
law origin_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.origin(L.Origin{h, s} <> rest, h) == s : L.Src}
