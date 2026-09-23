# ez/pin: a plain `ez lock` refuses a `[tools.*]` pin it would have to fill.
# It copies every pin as the ledger has it and never asks a remote, so a pin
# with no commit or no NAR hash stops it, naming the upgrade that fills the
# pin. Filling and moving a pin is `ez lock --upgrade`'s, in lock/up.bend.
import Base
import ../manifest/manifest.bend as M

# why a plain lock cannot copy a git pin as it stands, or "" when it can. The
# lock copies `rev` and `narHash` out of the ledger and never asks a remote
# for them, so a pin missing either is refused rather than filled, and the
# upgrade that fills it is named.
def gap.git(no_rev: Bool, no_nar: Bool, +name: String) -> String:
  match no_rev:
    case True{}:
      "ez: tools." ++ name ++ " has no rev; run `ez lock --upgrade --package " ++
        name ++ "` to pin it"
    case False{}:
      match no_nar:
        case True{}:
          "ez: tools." ++ name ++ " has no narHash; run `ez lock --upgrade --package " ++
            name ++ "` to pin it"
        case False{}:
          ""

# why a plain lock cannot copy a pin as it stands, or "" when it can. A pin
# with no repo has nothing to pin, under a plain lock or an upgrade.
def gap(pin: M.Tool) -> String:
  M.Tool{n, _e, _b, s} = pin
  match s:
    case M.Hub{}:
      "ez: tools." ++ n ++ " has no git"
    case M.Git{_url, rev, _tag, _root, nar, _vend}:
      gap.git(String.is_empty(rev), String.is_empty(nar), n)

# this pin's gap when it has one, otherwise the rest's. The rest arrives as a
# thunk and only the arm that wants it applies it, so the first gap stops the
# scan.
def gaps.step(none: Bool, here: String, rest: Unit -> String) -> String:
  match none:
    case True{}:
      rest(Unit{})
    case False{}:
      here

# the first pin, in ledger order, a plain lock cannot copy, or "" when it can
# copy every one
def gaps(ts: List<&2, M.Tool>) -> String:
  match ts:
    case []:
      ""
    case h <> t:
      +here = gap(h)
      gaps.step(String.is_empty(here), here, _u => gaps(t))
