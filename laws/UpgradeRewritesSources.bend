import Base
import ../src/ledger/upgrade.bend as U
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ./defs/LockInputs.bend as D1
import ./defs/WorldAfterLock.bend as D2

# LAW: a `.bend` source the upgrade read, once, holds afterwards its text
# with every moved hash rewritten, when `ez lock --upgrade` does not refuse.
# laws/UpgradeRewritesImports.bend and laws/RewriteKeepsOtherLines.bend say
# what that rewriting does to the text.
law upgrade_rewrites_sources:
  for +w: W.World
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for fs: {D1.found(w) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {D2.found.miss(pre, at) == True{} : Bool}
  for +mq: {D2.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for ok: {P.refuses(w) == False{} : Bool}
  {D2.left.at(P.put(w, at), text) == U.reimport.many(D2.swaps(w), text) : String}
