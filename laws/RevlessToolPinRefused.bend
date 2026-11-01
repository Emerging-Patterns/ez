import Base
import ../src/ledger/manifest.bend as M
import ../src/share/pin.bend as PinPin

# LAW: a git pin with no commit is refused, whatever else it holds, and the
# refusal names the upgrade that pins it
law gap_of_revless_pin:
  for +n: String
  for e: String
  for b: String
  for url: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  {PinPin.gap(M.Tool{n, e, b, M.Git{url, "", tag, root, nar, vend}})
    == "ez: tools." ++ n ++ " has no rev; run `ez lock --upgrade --package " ++
      n ++ "` to pin it" : String}
