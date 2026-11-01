import Base
import ../src/ledger/manifest.bend as M

# LAW: a ledger that did not read locks against bend's own hub. Nothing it
# said can be trusted, so nothing it said picks where packages come from.
law hub_of_unread_is_bends:
  for why: String
  {M.hub_of(M.Bad{why}) == "https://hub.bend-lang.com" : String}
