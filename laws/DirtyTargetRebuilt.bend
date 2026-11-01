# A local target with uncommitted or untracked changes, whatever the
# repository's own settings hide, or a path that is not the top of a checkout,
# resolves to no commit and is rebuilt on every run.
import Base
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# ---------------------------------------------------------------------------
# laws/DirtyTargetRebuilt.bend: a local target that is no commit

# LAW: a path `git status` names anything in is no commit
law local_rev_dirty:
  for +abs: String
  for +top: String
  for +head: String
  for ok: Bool
  for +status: String
  for d: {False{} == String.is_empty(status) : Bool}
  {TP.local.rev(abs, top, head, ok, status) == "" : String}

# LAW: nor is one `git status` did not answer for, which is not a checkout
law local_rev_unchecked:
  for +abs: String
  for +top: String
  for +head: String
  for +status: String
  {TP.local.rev(abs, top, head, False{}, status) == "" : String}

# LAW: nor is one that is not the top of its checkout
law local_rev_elsewhere:
  for +abs: String
  for +top: String
  for +head: String
  for ok: Bool
  for +status: String
  for e: {False{} == String.eq(top, abs) : Bool}
  {TP.local.rev(abs, top, head, ok, status) == "" : String}

# LAW: a target with no commit is built on every run
law tool_unrevved_builds:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  for none: {TP.rev(w) == "" : String}
  {TP.builds(TP.plan(w)) == True{} : Bool}
