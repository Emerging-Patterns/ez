import Base
import ../src/ledger/manifest.bend as M
import ../src/share/pin.bend as PinPin

# pin: a plain `ez lock` copies every `[tools.*]` pin as the ledger has it,
# and refuses one it would have to fill. Filling is `--upgrade`'s alone.

# LAW: a git pin with a commit and a NAR hash is copied as it is. Nothing
# about it asks the lock to reach a remote, so nothing stops the lock.
law gap_of_full_pin:
  for n: String
  for e: String
  for b: String
  for url: String
  for +rev: String
  for tag: String
  for root: String
  for +nar: String
  for vend: Bool
  for fr: {False{} == String.is_empty(rev) : Bool}
  for fn: {False{} == String.is_empty(nar) : Bool}
  {PinPin.gap(M.Tool{n, e, b, M.Git{url, rev, tag, root, nar, vend}}) == "" : String}
