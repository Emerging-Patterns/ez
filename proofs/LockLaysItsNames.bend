# proofs of laws/LockLaysItsNames.bend
import Base
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../laws/LockLaysItsNames.bend as Laws
import ../laws/defs/NamesLaid.bend as D1

# The names files a made lock lays: a line said, a tree laid, a file
# written and a tree removed lay none, and the names are laid from the lock's
# own text.

law nm.laid_says:
  for +ss: List<&2, String>
  for +rest: List<&2, P.Effect>
  {D1.names.laid(P.says.of(ss, rest)) == D1.names.laid(rest) : List<&2, L.Name>}

def nm.laid_says(ss, rest):
  match ss:
    case []:
      {==}
    case _h <> t:
      nm.laid_says(t, rest)

law nm.laid_pick:
  for +b: Bool
  for v: W.Verdict
  for pl: P.Place
  for +h: String
  for +rest: List<&2, P.Effect>
  {D1.names.laid(P.lay.pick(b, v, pl, h, rest)) == D1.names.laid(rest) : List<&2, L.Name>}

def nm.laid_pick(b, v, _pl, _h, _rest):
  match b:
    case True{}:
      match v:
        case W.No{_why}:
          {==}
        case W.Ok{_fs, _ss}:
          {==}
        case W.Named{_names}:
          {==}
    case False{}:
      {==}

law nm.laid_lays:
  for +cs: List<&2, String>
  for +vs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +rest: List<&2, P.Effect>
  {D1.names.laid(P.lays(cs, vs, js, rest)) == D1.names.laid(rest) : List<&2, L.Name>}

def nm.laid_lays(cs, vs, js, rest):
  match js:
    case []:
      {==}
    case W.Judged{+h, +v} <> +t:
      Equal.trans(List<&2, L.Name>,
        D1.names.laid(P.lay.pick(L.seen.holds(cs, h), v, P.place.of(L.seen.holds(vs, h)), h,
          P.lays(cs, vs, t, rest))),
        D1.names.laid(P.lays(cs, vs, t, rest)),
        D1.names.laid(rest),
        nm.laid_pick(L.seen.holds(cs, h), v, P.place.of(L.seen.holds(vs, h)), h,
          P.lays(cs, vs, t, rest)),
        nm.laid_lays(cs, vs, t, rest))

law nm.laid_names_lock:
  for +ns: List<&2, L.Name>
  for +rest: List<&2, P.Effect>
  {D1.names.laid(P.names.lay(ns, rest)) == List.append(&2, L.Name, ns, D1.names.laid(rest))
    : List<&2, L.Name>}

def nm.laid_names_lock(ns, rest):
  match ns:
    case []:
      {==}
    case L.Name{+nv, +hash} <> t:
      Equal.cong(List<&2, L.Name>, List<&2, L.Name>, r => L.Name{nv, hash} <> r,
        D1.names.laid(P.names.lay(t, rest)), List.append(&2, L.Name, t, D1.names.laid(rest)),
        nm.laid_names_lock(t, rest))

law nm.laid_edits:
  for +es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  {D1.names.laid(P.edits.of(es, rest)) == D1.names.laid(rest) : List<&2, L.Name>}

def nm.laid_edits(es, rest):
  match es:
    case []:
      {==}
    case Up.Edit{_at, _text} <> t:
      nm.laid_edits(t, rest)

law nm.laid_drops:
  for +ds: List<&2, String>
  for +rest: List<&2, P.Effect>
  {D1.names.laid(P.drops.of(ds, rest)) == D1.names.laid(rest) : List<&2, L.Name>}

def nm.laid_drops(ds, rest):
  match ds:
    case []:
      {==}
    case _h <> t:
      nm.laid_drops(t, rest)

# LAW: the upgrade's files, the trees it removes and the lock lay no names
# file
law nm.laid_tail:
  for +nx: Up.Next
  for +t: String
  {List.append(&2, L.Name, L.names.read(t), D1.names.laid(P.edits.of(Up.next.edits(nx),
    P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
      P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}])))))
    == L.names.read(t) : List<&2, L.Name>}

def nm.laid_tail(nx, t):
  %Equal.sym(List<&2, L.Name>, D1.names.laid(P.edits.of(Up.next.edits(nx),
      P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}])))),
      D1.names.laid(P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}]))),
      nm.laid_edits(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}]))))
    : {List.append(&2, L.Name, L.names.read(t), _) == L.names.read(t) : List<&2, L.Name>}
  %Equal.sym(List<&2, L.Name>, D1.names.laid(P.edits.of(Up.edit.sources(Up.next.found(nx),
        Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}]))),
      D1.names.laid(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}])),
      nm.laid_edits(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
        P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}])))
    : {List.append(&2, L.Name, L.names.read(t), _) == L.names.read(t) : List<&2, L.Name>}
  %Equal.sym(List<&2, L.Name>, D1.names.laid(P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}])),
      D1.names.laid([P.Write{P.lockfile(), t}]),
      nm.laid_drops(Up.next.drops(nx), [P.Write{P.lockfile(), t}]))
    : {List.append(&2, L.Name, L.names.read(t), _) == L.names.read(t) : List<&2, L.Name>}
  Str.list_append_nil(L.Name, L.names.read(t))

# LAW: a made lock lays the names of the lock it writes, and none other
law nm.made:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +t: String
  {D1.names.laid(P.effects(P.made(nx, cs, js, P.Doc{t}))) == L.names.read(t) : List<&2, L.Name>}

def nm.made(nx, cs, js, t):
  +tail = P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
    P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), t}])))
  +lays = P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(t), tail))
  Equal.trans(List<&2, L.Name>,
    D1.names.laid(P.says.of(Up.next.says(nx), lays)), D1.names.laid(lays), L.names.read(t),
    nm.laid_says(Up.next.says(nx), lays),
    Equal.trans(List<&2, L.Name>,
      D1.names.laid(lays), D1.names.laid(P.names.lay(L.names.read(t), tail)), L.names.read(t),
      nm.laid_lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(t), tail)),
      Equal.trans(List<&2, L.Name>,
        D1.names.laid(P.names.lay(L.names.read(t), tail)),
        List.append(&2, L.Name, L.names.read(t), D1.names.laid(tail)), L.names.read(t),
        nm.laid_names_lock(L.names.read(t), tail),
        nm.laid_tail(nx, t))))

def Laws.lock_lays_its_names(w, t, d):
  match w:
    case W.World{+args, +ledger, listing, +replies, +ups}:
      %d : {D1.names.laid(P.effects(P.made(W.next(args, ledger, ups),
          P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
          W.judged.of(W.next(args, ledger, ups), replies), _))) == L.names.read(t) : List<&2, L.Name>}
      nm.made(W.next(args, ledger, ups), P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies), t)
