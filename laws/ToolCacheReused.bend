# A cached binary is reused only when the recorded commit, built file and bend
# version all equal the resolved ones, and never when the resolved commit is
# empty. A cached checkout is reused only when its recorded commit equals the
# resolved one.
import Base
import ../src/ez/key.bend as KKey
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# key: when a cached tool is reused. The checkout is its commit; the binary
# is its commit, the file bend built and the bend that built it. Each law
# holds for every key, so no field is ever left out of the comparison.

# LAW: a binary built from another commit is built again
law key_rev_differs:
  for +r0: String
  for +f0: String
  for +b0: String
  for +r1: String
  for +f1: String
  for +b1: String
  for e: {False{} == String.eq(r0, r1) : Bool}
  {KKey.reuse(KKey.Stamp{r0, f0, b0}, KKey.Stamp{r1, f1, b1}) == False{} : Bool}

# LAW: a binary built from another file is built again, so a pin's `bin` or
# `entry` and a free run of the same commit do not share one
law key_file_differs:
  for +r0: String
  for +f0: String
  for +b0: String
  for +r1: String
  for +f1: String
  for +b1: String
  for e: {False{} == String.eq(f0, f1) : Bool}
  {KKey.reuse(KKey.Stamp{r0, f0, b0}, KKey.Stamp{r1, f1, b1}) == False{} : Bool}

# LAW: a binary another bend built is built again
law key_bend_differs:
  for +r0: String
  for +f0: String
  for +b0: String
  for +r1: String
  for +f1: String
  for +b1: String
  for e: {False{} == String.eq(b0, b1) : Bool}
  {KKey.reuse(KKey.Stamp{r0, f0, b0}, KKey.Stamp{r1, f1, b1}) == False{} : Bool}

# LAW: with no commit, whatever was recorded, the binary is built again
law key_no_rev:
  for was: KKey.Stamp
  for +f: String
  for +b: String
  {KKey.reuse(was, KKey.Stamp{"", f, b}) == False{} : Bool}

# LAW: the same commit, file and bend reuse the binary
law key_same_reuses:
  for +r: String
  for +f: String
  for +b: String
  for e: {False{} == String.is_empty(r) : Bool}
  {KKey.reuse(KKey.Stamp{r, f, b}, KKey.Stamp{r, f, b}) == True{} : Bool}

# LAW: a checkout of another commit is cloned again. The file and the bend
# are not asked.
law checkout_differs:
  for +was: String
  for +now: String
  for e: {False{} == String.eq(was, now) : Bool}
  {KKey.checkout(was, now) == False{} : Bool}

# LAW: a checkout of this commit is kept
law checkout_same:
  for +r: String
  for e: {False{} == String.is_empty(r) : Bool}
  {KKey.checkout(r, r) == True{} : Bool}

# ---------------------------------------------------------------------------
# laws/ToolCacheReused.bend: the binary's record, in the plan

# LAW: a binary that is there, with this record, is not built again
law tool_reuses_record:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for hit: {TP.reuse(w) == True{} : Bool}
  {TP.builds(TP.plan(w)) == False{} : Bool}

# LAW: any other is built
law tool_builds_on_miss:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.builds(TP.plan(w)) == True{} : Bool}
