import Base
import ../src/ledger/manifest.bend as M
import ../src/share/pin.bend as PinPin

# LAW: and one with a commit and no NAR hash is refused the same way
law gap_of_narless_pin:
  for +n: String
  for e: String
  for b: String
  for url: String
  for +rev: String
  for tag: String
  for root: String
  for vend: Bool
  for fr: {False{} == String.is_empty(rev) : Bool}
  {PinPin.gap(M.Tool{n, e, b, M.Git{url, rev, tag, root, "", vend}})
    == "ez: tools." ++ n ++ " has no narHash; run `ez lock --upgrade --package " ++
      n ++ "` to pin it" : String}
