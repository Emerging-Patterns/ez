# proofs of laws/TailOne.bend
import Base
import ../src/pkg/path.bend as Path
import ../laws/TailOne.bend as Laws

# LAW: taking nothing off a list is the empty list
law take_zero:
  for xs: List<&2, String>
  {List.take(&2, String, xs, 0n) == [] : List<&2, String>}

def take_zero(xs):
  match xs:
    case []:
      {==}
    case _h <> _t:
      {==}

# LAW: the first of a reversed list does not depend on what was already
# behind the head of the accumulator
law take_rev_go_acc:
  for xs: List<&2, String>
  for +a: String
  for acc: List<&2, String>
  {List.take(&2, String, List.reverse.go(&2, String, xs, a <> acc), 1n)
    == List.take(&2, String, List.reverse.go(&2, String, xs, [a]), 1n)
    : List<&2, String>}

def take_rev_go_acc(xs, a, acc):
  match xs:
    case []:
      Equal.trans(List<&2, String>,
        a <> List.take(&2, String, acc, 0n),
        a <> [],
        [a],
        Equal.cong(List<&2, String>, List<&2, String>, r => a <> r,
          List.take(&2, String, acc, 0n), [], take_zero(acc)),
        {==})
    case +h <> +t:
      Equal.trans(List<&2, String>,
        List.take(&2, String, List.reverse.go(&2, String, t, h <> (a <> acc)),
          1n),
        List.take(&2, String, List.reverse.go(&2, String, t, [h]), 1n),
        List.take(&2, String, List.reverse.go(&2, String, t, h <> [a]), 1n),
        take_rev_go_acc(t, h, a <> acc),
        Equal.sym(List<&2, String>,
          List.take(&2, String, List.reverse.go(&2, String, t, h <> [a]), 1n),
          List.take(&2, String, List.reverse.go(&2, String, t, [h]), 1n),
          take_rev_go_acc(t, h, [a])))

# LAW: taking one off a reversed list is the last component
law take_rev_last:
  for t: List<&2, String>
  for +h: String
  {List.take(&2, String, List.reverse.go(&2, String, t, [h]), 1n)
    == [Path.base.go(t, h)] : List<&2, String>}

def take_rev_last(t, h):
  match t:
    case []:
      {==}
    case +a <> +r:
      Equal.trans(List<&2, String>,
        List.take(&2, String, List.reverse.go(&2, String, r, a <> [h]), 1n),
        List.take(&2, String, List.reverse.go(&2, String, r, [a]), 1n),
        [Path.base.go(r, a)],
        take_rev_go_acc(r, a, [h]),
        take_rev_last(r, a))

# LAW: taking the last component of a split list is `base.last` of it
law tail_one.go:
  for ps: List<&2, String>
  {String.join(List.reverse(&2, String,
    List.take(&2, String, List.reverse(&2, String, ps), 1n)), "/")
    == Path.base.last(ps) : String}

def tail_one.go(ps):
  match ps:
    case []:
      {==}
    case +h <> t:
      Equal.trans(String,
        String.join(List.reverse(&2, String,
          List.take(&2, String, List.reverse(&2, String, h <> t), 1n)), "/"),
        String.join(List.reverse(&2, String, [Path.base.go(t, h)]), "/"),
        Path.base.go(t, h),
        Equal.cong(List<&2, String>, String,
          xs => String.join(List.reverse(&2, String, xs), "/"),
          List.take(&2, String, List.reverse.go(&2, String, t, [h]), 1n),
          [Path.base.go(t, h)], take_rev_last(t, h)),
        Equal.trans(String,
          String.join(List.reverse(&2, String, [Path.base.go(t, h)]), "/"),
          String.join([Path.base.go(t, h)], "/"),
          Path.base.go(t, h),
          {==},
          {==}))

def Laws.tail_one(p):
  tail_one.go(String.split(p, '/'))
