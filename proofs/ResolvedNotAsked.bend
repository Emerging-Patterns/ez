# proofs of laws/ResolvedNotAsked.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../laws/ResolvedNotAsked.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1

def Laws.lock_answer_names(_orgs, _hub, _key, _text):
  {==}

# The names put to the hub are the names still open, once and in order, so a
# name the table resolves is none of them.

# LAW: a list of names none of which is this one asks the hub nothing of it
law nm.asked_none:
  for +hub: String
  for +xs: List<&2, String>
  for +nv: String
  for +e: {L.seen.holds(xs, nv) == False{} : Bool}
  {Laws.asks.name(P.names.asked(hub, xs), nv) == False{} : Bool}

def nm.asked_none(hub, xs, nv, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, String.eq(h, nv), False{},
        M1.any_head(String.eq(h, nv), _u => L.seen.holds(t, nv), e))
        : {L.any.step(_, _u => Laws.asks.name(P.names.asked(hub, t), nv)) == False{} : Bool}
      nm.asked_none(hub, t, nv, M1.any_rest(String.eq(h, nv), _u => L.seen.holds(t, nv), e))

# LAW: a name kept once, with whether it was seen already decided
law nm.once.step:
  for +b: Bool
  for +h: String
  for +rest: List<&2, String>
  for +nv: String
  for +eh: {String.eq(h, nv) == False{} : Bool}
  for +er: {L.seen.holds(rest, nv) == False{} : Bool}
  {L.seen.holds(P.names.once.put(b, h, rest), nv) == False{} : Bool}

def nm.once.step(b, h, rest, nv, eh, er):
  match b:
    case True{}:
      er
    case False{}:
      %Equal.sym(Bool, String.eq(h, nv), False{}, eh)
        : {L.any.step(_, _u => L.seen.holds(rest, nv)) == False{} : Bool}
      er

# LAW: names kept once hold nothing the names did not
law nm.once_none:
  for +xs: List<&2, String>
  for +seen: List<&2, String>
  for +nv: String
  for +e: {L.seen.holds(xs, nv) == False{} : Bool}
  {L.seen.holds(P.names.once(xs, seen), nv) == False{} : Bool}

def nm.once_none(xs, seen, nv, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      nm.once.step(L.seen.holds(seen, h), h, P.names.once(t, h <> seen), nv,
        M1.any_head(String.eq(h, nv), _u => L.seen.holds(t, nv), e),
        nm.once_none(t, h <> seen, nv, M1.any_rest(String.eq(h, nv), _u => L.seen.holds(t, nv), e)))

# LAW: an open name is not the one the table resolves: were it, the table
# would resolve it
law nm.open.hit:
  for +c: Bool
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +roots: List<&2, String>
  for +h: String
  for +rest: List<&2, String>
  for +nv: String
  for +ec: {c == String.eq(h, nv) : Bool}
  for +eb: {True{} == P.name.open(ns, js, roots, h) : Bool}
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  for +er: {L.seen.holds(rest, nv) == False{} : Bool}
  {L.any.step(c, _u => L.seen.holds(rest, nv)) == False{} : Bool}

def nm.open.hit(c, ns, js, roots, h, rest, nv, ec, eb, f, er):
  match c:
    case False{}:
      er
    case True{}:
      +hn = Str.string_eq_true(h, nv, Equal.sym(Bool, True{}, String.eq(h, nv), ec))
      +o = Equal.trans(Bool, P.name.open(ns, js, roots, nv), P.name.open(ns, js, roots, h), True{},
        Equal.cong(String, Bool, x => P.name.open(ns, js, roots, x), nv, h,
          Equal.sym(String, h, nv, hn)),
        Equal.sym(Bool, True{}, P.name.open(ns, js, roots, h), eb))
      +emp = Eq.and.left(String.is_empty(L.name.find(ns, nv)),
        Bool.and(Bool.not(L.seen.holds(roots, nv)), P.is.absent(P.look(js, nv))),
        Eq.and.right(K.name.ok(nv), Bool.and(String.is_empty(L.name.find(ns, nv)),
          Bool.and(Bool.not(L.seen.holds(roots, nv)), P.is.absent(P.look(js, nv)))), o))
      Eq.bit.absurd(&2, {L.any.step(True{}, _u => L.seen.holds(rest, nv)) == False{} : Bool},
        Equal.trans(Bool, False{}, String.is_empty(L.name.find(ns, nv)), True{}, f, emp))

# LAW: one name kept open, with whether it is open decided: a name the table
# resolves never is
law nm.open.step:
  for +b: Bool
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +roots: List<&2, String>
  for +h: String
  for +rest: List<&2, String>
  for +nv: String
  for +eb: {b == P.name.open(ns, js, roots, h) : Bool}
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  for +er: {L.seen.holds(rest, nv) == False{} : Bool}
  {L.seen.holds(P.names.open.put(b, h, rest), nv) == False{} : Bool}

def nm.open.step(b, ns, js, roots, h, rest, nv, eb, f, er):
  match b:
    case False{}:
      er
    case True{}:
      nm.open.hit(String.eq(h, nv), ns, js, roots, h, rest, nv, {==}, eb, f, er)

# LAW: no name still open is one the table resolves
law nm.open_none:
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +roots: List<&2, String>
  for +nvs: List<&2, String>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  {L.seen.holds(P.names.open(ns, js, roots, nvs), nv) == False{} : Bool}

def nm.open_none(ns, js, roots, nvs, nv, f):
  match nvs:
    case []:
      {==}
    case +h <> +t:
      nm.open.step(P.name.open(ns, js, roots, h), ns, js, roots, h, P.names.open(ns, js, roots, t),
        nv, {==}, f, nm.open_none(ns, js, roots, t, nv, f))

# LAW: the questions for names that do not hold this one ask nothing of it,
# the lock's question included, with whether the lock was read decided
law nm.ask.lock_none:
  for +b: Bool
  for +hub: String
  for +nvs: List<&2, String>
  for +nv: String
  for +e: {L.seen.holds(nvs, nv) == False{} : Bool}
  {Laws.asks.name(P.names.ask.lock(b, hub, nvs), nv) == False{} : Bool}

def nm.ask.lock_none(b, hub, nvs, nv, e):
  match b:
    case True{}:
      nm.asked_none(hub, P.names.once(nvs, []), nv, nm.once_none(nvs, [], nv, e))
    case False{}:
      {==}

law nm.ask_none:
  for +hub: String
  for +js: List<&2, W.Judged>
  for +nvs: List<&2, String>
  for +nv: String
  for +e: {L.seen.holds(nvs, nv) == False{} : Bool}
  {Laws.asks.name(P.names.ask(hub, js, nvs), nv) == False{} : Bool}

def nm.ask_none(hub, js, nvs, nv, e):
  match nvs:
    case []:
      {==}
    case +h <> +t:
      nm.ask.lock_none(Bool.not(P.is.absent(P.look(js, W.lockfile()))), hub, h <> t, nv, e)

law nm.bad_none:
  for +clean: Bool
  for +led: M.Read
  for +listing: W.Listing
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +packs: List<&2, L.Pack>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  {Laws.asks.name(P.names.wants.bad(clean, led, listing, ns, js, packs), nv) == False{} : Bool}

def nm.bad_none(clean, led, listing, ns, js, packs, nv, f):
  match clean:
    case True{}:
      nm.ask_none(M.hub_of(led), js,
        P.names.open(ns, js, P.roots.named(P.listing.files(listing)), P.packs.named(js, packs)), nv,
        nm.open_none(ns, js, P.roots.named(P.listing.files(listing)), P.packs.named(js, packs), nv, f))
    case False{}:
      {==}

law nm.walk_none:
  for +wk: P.Walk
  for +led: M.Read
  for +listing: W.Listing
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  {Laws.asks.name(P.names.wants.walk(wk, led, listing, ns, js), nv) == False{} : Bool}

def nm.walk_none(wk, led, listing, ns, js, nv, f):
  match wk:
    case P.Walk{_q, packs, _a, +bad}:
      nm.bad_none(String.is_empty(bad), led, listing, ns, js, packs, nv, f)

law nm.gap_none:
  for +clean: Bool
  for +led: M.Read
  for +listing: W.Listing
  for +js: List<&2, W.Judged>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.find(P.table(led, js), nv)) : Bool}
  {Laws.asks.name(P.names.wants.gap(clean, led, listing, js), nv) == False{} : Bool}

def nm.gap_none(clean, led, listing, js, nv, f):
  match clean:
    case True{}:
      nm.walk_none(P.walk.of(led, listing, P.table(led, js), js), led, listing, P.table(led, js), js,
        nv, f)
    case False{}:
      {==}

law nm.stop_none:
  for +clean: Bool
  for +led: M.Read
  for +listing: W.Listing
  for +js: List<&2, W.Judged>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.find(P.table(led, js), nv)) : Bool}
  {Laws.asks.name(P.names.wants.stop(clean, led, listing, js), nv) == False{} : Bool}

def nm.stop_none(clean, led, listing, js, nv, f):
  match clean:
    case True{}:
      nm.gap_none(String.is_empty(P.need.why(led)), led, listing, js, nv, f)
    case False{}:
      {==}

def Laws.resolved_not_asked(w, nv, r):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      nm.stop_none(String.is_empty(Up.next.stop(W.next(args, ledger, ups))),
        Up.next.read(W.next(args, ledger, ups)), W.listing.of(W.next(args, ledger, ups), listing),
        P.scan(W.replies.of(W.next(args, ledger, ups), replies)), nv, r)
