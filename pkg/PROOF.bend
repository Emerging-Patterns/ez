# pkg: the proofs. `bend PROOF.bend` is the gate.
#
# What is not here: that `files_of` answers the same list whatever order the
# walk found the files in. That is a property of Base's `List.sort`, a fuelled
# bottom-up merge sort, and stating it needs lemmas about `List.merge` that
# Base does not carry. `tests/publish.sh` holds that end down instead, by
# running the real `bend --publish` against a local hub.
import Base
import ./pkg.bend as P
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# LAW: one step of the deduplication, with the branch the pick takes given as
# a parameter and the equation that put it there given alongside, since a
# match may not scrutinise a computed value
law dedup_dup.arm:
  for +f: P.File
  for b: P.File
  for t: List<&2, P.File>
  for bb: Bool
  for eb: {String.eq(P.file.at(f), P.file.at(b)) == bb : Bool}
  {P.dedup.head(f, P.dedup.pick(bb, f, b <> t)) == P.dedup.pick(bb, f, b <> t)
    : List<&2, P.File>}

def dedup_dup.arm(f, b, t, bb, eb):
  match bb:
    case True{}:
      Equal.cong(Bool, List<&2, P.File>, x => P.dedup.pick(x, f, b <> t),
        String.eq(P.file.at(f), P.file.at(b)), True{}, eb)
    case False{}:
      Equal.cong(Bool, List<&2, P.File>,
        x => P.dedup.pick(x, f, f <> (b <> t)),
        String.eq(P.file.at(f), P.file.at(f)), True{},
        Eq.string_eq_self(P.file.at(f)))

# LAW: offering the same file to a deduplicated list twice changes nothing
law dedup_dup.head:
  for +f: P.File
  for r: List<&2, P.File>
  {P.dedup.head(f, P.dedup.head(f, r)) == P.dedup.head(f, r)
    : List<&2, P.File>}

def dedup_dup.head(f, r):
  match r:
    case []:
      Equal.cong(Bool, List<&2, P.File>, x => P.dedup.pick(x, f, [f]),
        String.eq(P.file.at(f), P.file.at(f)), True{},
        Eq.string_eq_self(P.file.at(f)))
    case +b <> t:
      dedup_dup.arm(f, b, t, String.eq(P.file.at(f), P.file.at(b)), {==})

def Laws.dedup_dup(f, t):
  dedup_dup.head(f, P.dedup(t))

# LAW: whichever branch the pick takes, what comes back is a file and a rest
law dedup_keeps.arm:
  for -f: P.File
  for -b: P.File
  for -t: List<&2, P.File>
  for bb: Bool
  {List.is_empty(&2, P.File, P.dedup.pick(bb, f, b <> t)) == False{} : Bool}

def dedup_keeps.arm(f, b, t, bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a file offered to any deduplicated list comes back with it
law dedup_keeps.head:
  for +h: P.File
  for r: List<&2, P.File>
  {List.is_empty(&2, P.File, P.dedup.head(h, r)) == False{} : Bool}

def dedup_keeps.head(h, r):
  match r:
    case []:
      {==}
    case +b <> t:
      dedup_keeps.arm(h, b, t, String.eq(P.file.at(h), P.file.at(b)))

def Laws.dedup_keeps(h, t):
  dedup_keeps.head(h, P.dedup(t))
