# proofs of laws/PlainLockKeepsLedger.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../laws/PlainLockKeepsLedger.bend as Laws
import ../laws/WalkPinsLedgerSources.bend as L1
import ../laws/defs/LockInputs.bend as D1
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

# LAW: and a plain lock leaves nothing at ez.toml, whatever was decided
law made_keeps_ledger:
  for +led: M.Read
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  {P.put.plan(P.made(Up.plain(led), cs, js, d), "ez.toml") == P.Kept{} : P.Wrote}

def made_keeps_ledger(_led, cs, js, d):
  match d:
    case P.Doc{+text}:
      M2.lays_names_put(cs, [], js, L.names.read(text), [P.Write{P.lockfile(), text}], "ez.toml")
    case P.Stop{_why}:
      {==}

# A plain lock's World is one whose args say no `--upgrade`; the other arm
# contradicts the premise.
def Laws.plain_lock_keeps_ledger(w, e):
  match w:
    case W.World{args, +ledger, listing, +replies, ups}:
      match args:
        case W.Args{up, only, here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.put(W.World{W.Args{True{}, only, here}, ledger, listing,
                replies, ups}, "ez.toml") == P.Kept{} : P.Wrote}, e)
            case False{}:
              made_keeps_ledger(W.parsed(ledger),
                P.cloned(W.replies.of(Up.plain(W.parsed(ledger)), replies)),
                W.judged.of(Up.plain(W.parsed(ledger)), replies),
                P.decide(W.Inputs{W.parsed(ledger), "", listing,
                  W.judged.of(Up.plain(W.parsed(ledger)), replies)}))

def Laws.plain_lock_pins_ledger_sources(w, e):
  match w:
    case W.World{args, +ledger, listing, +replies, ups}:
      match args:
        case W.Args{up, only, here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {D1.pinned.all(W.origins(ledger),
                P.packs(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups}))
                == P.packs(W.World{W.Args{True{}, only, here}, ledger, listing, replies, ups})
                : List<&2, L.Pack>}, e)
            case False{}:
              match listing:
                case W.Unlisted{why}:
                  {==}
                case W.Listed{+fs}:
                  L1.walk_pins_ledger_sources(
                    P.walk.fuel(List.append(&2, String, P.roots(fs),
                      L.name.hashes(P.table(W.parsed(ledger), W.judge(W.origins(ledger),
                        W.ledger.hub(ledger), replies)), P.roots.named(fs))),
                      P.table(W.parsed(ledger), W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)),
                      W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)),
                    L.ledger.read(W.parsed(ledger)),
                    P.table(W.parsed(ledger), W.judge(W.origins(ledger), W.ledger.hub(ledger), replies)),
                    W.judge(W.origins(ledger), W.ledger.hub(ledger), replies),
                    P.Walk{List.append(&2, String, P.roots(fs),
                      L.name.hashes(P.table(W.parsed(ledger), W.judge(W.origins(ledger),
                        W.ledger.hub(ledger), replies)), P.roots.named(fs))), [], [], ""}, {==})
