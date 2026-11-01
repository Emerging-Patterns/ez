# `ez lock` asks the hub what a name names only when neither the ledger the
# lock is made from (ez.toml, or in a workspace the joint ledger) nor the lock
# being rewritten records it.
import Base
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up

# whether a question puts this name to the hub. Law vocabulary.
def ask.named(ask: W.Ask, +nv: String) -> Bool:
  match ask:
    case W.Name{n, _hub}:
      String.eq(n, nv)
    case _:
      False{}

# whether a list of questions puts this name to the hub. Law vocabulary.
def asks.name(as: List<&2, W.Ask>, +nv: String) -> Bool:
  match as:
    case []:
      False{}
    case h <> t:
      L.any.step(ask.named(h, nv), _u => asks.name(t, nv))

# the table of names the lock resolves names by on a World, as its questions
# are asked: ez.toml's names first, then those the answers resolve. Law
# vocabulary.
def names.table(world: W.World) -> List<&2, L.Name>:
  W.World{+args, +ledger, _listing, replies, +ups} = world
  P.table(Up.next.read(W.next(args, ledger, ups)),
    P.scan(W.replies.of(W.next(args, ledger, ups), replies)))

# LAW: the lock being rewritten, read, resolves every name it records that
# bend would read back, so those names join the table without the hub
law lock_answer_names:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +key: String
  for text: String
  {W.accept(orgs, hub, key, W.Locked{text}) == W.Named{L.names.read(text)} : W.Verdict}

# LAW: a name the table resolves, because ez.toml records it or the lock
# being rewritten does, is never put to the hub
law resolved_not_asked:
  for +w: W.World
  for +nv: String
  for r: {False{} == String.is_empty(L.name.find(names.table(w), nv)) : Bool}
  {asks.name(P.wants.names(w), nv) == False{} : Bool}
