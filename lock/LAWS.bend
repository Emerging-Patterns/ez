# lock: the laws. The human states them; PROOF.bend must prove them. The one
# decision the pure half of the lock makes is where a package's bytes come
# from, and a wrong answer there is a lock that rebuilds the wrong tree
# without ever saying so.
import Base
import ./lock.bend as L

# LAW: a package resolves to the origin recorded for it, whatever origins
# follow. A second record of the same hash never shadows the first, so each of
# ez.toml and `.ez/origins.toml` is read the way it was written.
law origin_first:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.origin(L.Origin{h, s} <> rest, h) == s : L.Src}

# LAW: a package resolves to the same origin whether the ledger recorded it or
# the cache did. This is the property the tool exists for: a fresh clone has
# ez.toml and no `.ez/origins.toml` at all, and it must lock what a working
# checkout locks. It also says the ledger wins outright, since the cache it is
# quantified over is any cache, including one recording the same hash
# differently.
law origin_agrees:
  for +h: String
  for +s: L.Src
  for cache: List<&2, L.Origin>
  {L.origin(L.origins.all([L.Origin{h, s}], cache), h)
    == L.origin(L.origins.all([], [L.Origin{h, s}]), h) : L.Src}
