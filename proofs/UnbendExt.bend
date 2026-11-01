# proofs of laws/UnbendExt.bend
import Base
import ../src/check/eq.bend as Eq
import ../laws/UnbendExt.bend as Laws
import ./lemmas/NatSubSelf.bend as M1

# LAW: reversing a concatenation is concatenating the reverses
law reverse_go_app:
  for a: String
  for +b: String
  for +acc: String
  {String.reverse.go(String.append(a, b), acc)
    == String.reverse.go(b, String.reverse.go(a, acc)) : String}

def reverse_go_app(a, b, acc):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      reverse_go_app(t, b, SCon{h, acc})

# LAW: the accumulator of a reverse is appended after what was reversed
law reverse_go_acc:
  for s: String
  for +acc: String
  {String.reverse.go(s, acc)
    == String.append(String.reverse.go(s, SNil{}), acc) : String}

def reverse_go_acc(s, acc):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String,
        String.reverse.go(t, SCon{h, acc}),
        String.append(String.reverse.go(t, SNil{}), SCon{h, acc}),
        String.append(String.reverse.go(SCon{h, t}, SNil{}), acc),
        reverse_go_acc(t, SCon{h, acc}),
        Equal.trans(String,
          String.append(String.reverse.go(t, SNil{}), SCon{h, acc}),
          String.append(String.append(String.reverse.go(t, SNil{}),
            SCon{h, SNil{}}), acc),
          String.append(String.reverse.go(t, SCon{h, SNil{}}), acc),
          Equal.sym(String,
            String.append(String.append(String.reverse.go(t, SNil{}),
              SCon{h, SNil{}}), acc),
            String.append(String.reverse.go(t, SNil{}), SCon{h, acc}),
            Eq.append_assoc(String.reverse.go(t, SNil{}), SCon{h, SNil{}},
              acc)),
          Equal.cong(String, String, x => String.append(x, acc),
            String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}),
            String.reverse.go(t, SCon{h, SNil{}}),
            Equal.sym(String,
              String.reverse.go(t, SCon{h, SNil{}}),
              String.append(String.reverse.go(t, SNil{}), SCon{h, SNil{}}),
              reverse_go_acc(t, SCon{h, SNil{}})))))

law reverse_append:
  for +a: String
  for +b: String
  {String.reverse(String.append(a, b))
    == String.append(String.reverse(b), String.reverse(a)) : String}

def reverse_append(a, b):
  Equal.trans(String,
    String.reverse.go(String.append(a, b), SNil{}),
    String.reverse.go(b, String.reverse.go(a, SNil{})),
    String.append(String.reverse.go(b, SNil{}), String.reverse.go(a, SNil{})),
    reverse_go_app(a, b, SNil{}),
    reverse_go_acc(b, String.reverse.go(a, SNil{})))

# LAW: a string with `.bend` glued on ends with `.bend`
law ends_bend:
  for +p: String
  {String.ends_with(p ++ ".bend", ".bend") == True{} : Bool}

def ends_bend(p):
  Equal.trans(Bool,
    String.starts_with(String.reverse(p ++ ".bend"), String.reverse(".bend")),
    String.starts_with(String.append(String.reverse(".bend"), String.reverse(p)),
      String.reverse(".bend")),
    True{},
    Equal.cong(String, Bool,
      s => String.starts_with(s, String.reverse(".bend")),
      String.reverse(p ++ ".bend"),
      String.append(String.reverse(".bend"), String.reverse(p)),
      reverse_append(p, ".bend")),
    Eq.starts_append(String.reverse(".bend"), String.reverse(p)))

# LAW: taking as many characters as a prefix has leaves the prefix
law take_prefix:
  for +p: String
  for +s: String
  {String.take(String.append(p, s), String.length(p)) == p : String}

def take_prefix(p, s):
  match p:
    case SNil{}:
      match s:
        case SNil{}:
          {==}
        case SCon{_h, _t}:
          {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.take(String.append(t, s), String.length(t)), t,
        take_prefix(t, s))

# LAW: length adds over a concatenation
law length_append:
  for a: String
  for +b: String
  {String.length(String.append(a, b))
    == Nat.add(String.length(a), String.length(b)) : Nat}

def length_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{_h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        String.length(String.append(t, b)),
        Nat.add(String.length(t), String.length(b)),
        length_append(t, b))

# LAW: subtracting zero leaves the number
law sub_zero:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

def sub_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+_p:
      {==}

# LAW: adding a successor on the right is a successor
law add_succ_right:
  for n: Nat
  for +m: Nat
  {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}

def add_succ_right(n, m):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x,
        Nat.add(p, 1n+m), 1n+Nat.add(p, m), add_succ_right(p, m))

# LAW: subtracting from one more than `n+m` peels the same as subtracting
# from `n+m`, plus one. Used to carry a successor across `add_sub`.
law sub_add_succ:
  for +p: Nat
  for +m: Nat
  {Nat.sub(1n+Nat.add(p, m), m) == 1n+Nat.sub(Nat.add(p, m), m) : Nat}

def sub_add_succ(p, m):
  match m:
    case 0n:
      Equal.cong(Nat, Nat, k => 1n+k,
        Nat.add(p, 0n), Nat.sub(Nat.add(p, 0n), 0n),
        Equal.sym(Nat, Nat.sub(Nat.add(p, 0n), 0n), Nat.add(p, 0n),
          sub_zero(Nat.add(p, 0n))))
    case 1n+q:
      Equal.trans(Nat,
        Nat.sub(Nat.add(p, 1n+q), q),
        Nat.sub(1n+Nat.add(p, q), q),
        1n+Nat.sub(Nat.add(p, 1n+q), 1n+q),
        Equal.cong(Nat, Nat, k => Nat.sub(k, q),
          Nat.add(p, 1n+q), 1n+Nat.add(p, q), add_succ_right(p, q)),
        Equal.trans(Nat,
          Nat.sub(1n+Nat.add(p, q), q),
          1n+Nat.sub(Nat.add(p, q), q),
          1n+Nat.sub(Nat.add(p, 1n+q), 1n+q),
          sub_add_succ(p, q),
          Equal.cong(Nat, Nat, k => 1n+k,
            Nat.sub(Nat.add(p, q), q),
            Nat.sub(Nat.add(p, 1n+q), 1n+q),
            Equal.sym(Nat, Nat.sub(Nat.add(p, 1n+q), 1n+q),
              Nat.sub(Nat.add(p, q), q),
              Equal.trans(Nat,
                Nat.sub(Nat.add(p, 1n+q), 1n+q),
                Nat.sub(1n+Nat.add(p, q), 1n+q),
                Nat.sub(Nat.add(p, q), q),
                Equal.cong(Nat, Nat, k => Nat.sub(k, 1n+q),
                  Nat.add(p, 1n+q), 1n+Nat.add(p, q),
                  add_succ_right(p, q)),
                {==})))))

# LAW: adding a number and taking it off leaves the first
law add_sub:
  for +n: Nat
  for +m: Nat
  {Nat.sub(Nat.add(n, m), m) == n : Nat}

def add_sub(n, m):
  match n:
    case 0n:
      M1.sub_self(m)
    case 1n+p:
      Equal.trans(Nat,
        Nat.sub(1n+Nat.add(p, m), m),
        1n+Nat.sub(Nat.add(p, m), m),
        1n+p,
        sub_add_succ(p, m),
        Equal.cong(Nat, Nat, k => 1n+k,
          Nat.sub(Nat.add(p, m), m), p, add_sub(p, m)))

def Laws.unbend_ext(p):
  Equal.trans(String,
    Bool.pick(String, String.ends_with(p ++ ".bend", ".bend"),
      String.take(p ++ ".bend", Nat.sub(String.length(p ++ ".bend"), 5n)),
      p ++ ".bend"),
    Bool.pick(String, True{},
      String.take(p ++ ".bend", Nat.sub(String.length(p ++ ".bend"), 5n)),
      p ++ ".bend"),
    p,
    Equal.cong(Bool, String,
      x => Bool.pick(String, x,
        String.take(p ++ ".bend", Nat.sub(String.length(p ++ ".bend"), 5n)),
        p ++ ".bend"),
      String.ends_with(p ++ ".bend", ".bend"), True{}, ends_bend(p)),
    Equal.trans(String,
      String.take(p ++ ".bend", Nat.sub(String.length(p ++ ".bend"), 5n)),
      String.take(p ++ ".bend", String.length(p)),
      p,
      Equal.cong(Nat, String, n => String.take(p ++ ".bend", n),
        Nat.sub(String.length(p ++ ".bend"), 5n), String.length(p),
        Equal.trans(Nat,
          Nat.sub(String.length(String.append(p, ".bend")), 5n),
          Nat.sub(String.length(String.append(p, ".bend")),
            String.length(".bend")),
          String.length(p),
          Equal.cong(Nat, Nat,
            n => Nat.sub(String.length(String.append(p, ".bend")), n),
            5n, String.length(".bend"), {==}),
          Equal.trans(Nat,
            Nat.sub(String.length(String.append(p, ".bend")),
              String.length(".bend")),
            Nat.sub(Nat.add(String.length(p), String.length(".bend")),
              String.length(".bend")),
            String.length(p),
            Equal.cong(Nat, Nat, n => Nat.sub(n, String.length(".bend")),
              String.length(String.append(p, ".bend")),
              Nat.add(String.length(p), String.length(".bend")),
              length_append(p, ".bend")),
            add_sub(String.length(p), String.length(".bend"))))),
      take_prefix(p, ".bend")))
