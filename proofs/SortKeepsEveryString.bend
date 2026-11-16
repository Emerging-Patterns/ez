# proofs of laws/SortKeepsEveryString.bend
import Base
import ../src/ez/sorted.bend as Sort
import ../laws/SortKeepsEveryString.bend as Laws

# LAW: the choice an insertion makes keeps the count, whichever it is
law put_adds_one:
  for le: Bool
  for +item: String
  for +h: String
  for t: List<&2, String>
  for ih: {List.length(&2, String, Sort.sort.ins(item, t)) == 1n+List.length(&2, String, t) : Nat}
  {List.length(&2, String, Sort.sort.ins.put(le, item, h, t, Sort.sort.ins(item, t)))
    == 1n+1n+List.length(&2, String, t) : Nat}

def put_adds_one(le, item, _h, t, ih):
  match le:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, List.length(&2, String, Sort.sort.ins(item, t)), 1n+List.length(&2, String, t), ih)
        : {1n+_ == 1n+1n+List.length(&2, String, t) : Nat}
      {==}

def Laws.ins_adds_one(item, ss):
  match ss:
    case []:
      {==}
    case +h <> +t:
      put_adds_one(String.is_le(item, h), item, h, t, Laws.ins_adds_one(item, t))

def Laws.sort_keeps_length(ss):
  match ss:
    case []:
      {==}
    case +h <> +t:
      %Laws.sort_keeps_length(t)
        : {List.length(&2, String, Sort.sort.ins(h, Sort.sort(t))) == 1n+_ : Nat}
      Laws.ins_adds_one(h, Sort.sort(t))
