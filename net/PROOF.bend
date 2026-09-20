# net: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./http.bend as Http
import ./url.bend as Url
import ./LAWS.bend as Laws

# LAW: one step of the partition, with the branch the pick takes given as a
# parameter, since a match may not scrutinise a computed value
law utf8_split.arm:
  for -h: Char
  for -t: String
  for -m: Nat
  for b: Bool
  for ih: {String.append(Http.utf8.take(t, m), Http.utf8.drop(t, m)) == t : String}
  {String.append(
    Bool.pick(String, b, SNil{}, SCon{h, Http.utf8.take(t, m)}),
    Bool.pick(String, b, SCon{h, t}, Http.utf8.drop(t, m))) == SCon{h, t} : String}

def utf8_split.arm(h, t, m, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(Http.utf8.take(t, m), Http.utf8.drop(t, m)), t, ih)

def Laws.utf8_split(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      utf8_split.arm(h, t, Nat.sub(n, Http.utf8.width(Char.to_u32(h))),
        Nat.is_lt(n, Http.utf8.width(Char.to_u32(h))),
        Laws.utf8_split(t, Nat.sub(n, Http.utf8.width(Char.to_u32(h)))))

# LAW: nothing is below zero
law lt_zero:
  for n: Nat
  {Nat.is_lt(n, 0n) == False{} : Bool}

def lt_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# LAW: a sum is never below the part it was built from
law lt_add:
  for a: Nat
  for +b: Nat
  {Nat.is_lt(Nat.add(a, b), a) == False{} : Bool}

def lt_add(a, b):
  match a:
    case 0n:
      lt_zero(b)
    case 1n+p:
      lt_add(p, b)

# LAW: nothing is below itself
law lt_self:
  for n: Nat
  {Nat.is_lt(n, n) == False{} : Bool}

def lt_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_self(p)

# LAW: taking nothing off leaves the whole
law sub_zero:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

def sub_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# LAW: taking a part back off the sum it went into leaves the other part
law sub_add:
  for a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), a) == b : Nat}

def sub_add(a, b):
  match a:
    case 0n:
      sub_zero(b)
    case 1n+p:
      sub_add(p, b)

# LAW: a string taken to its own byte count is the whole string
law take_all:
  for +s: String
  {Http.utf8.take(s, Http.utf8.len(s)) == s : String}

def take_all(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String,
        Http.utf8.take(SCon{h, t}, Http.utf8.len(SCon{h, t})),
        SCon{h, Http.utf8.take(t, Nat.sub(
          Nat.add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t)),
          Http.utf8.width(Char.to_u32(h))))},
        SCon{h, t},
        Equal.cong(Bool, String,
          b => Bool.pick(String, b, SNil{}, SCon{h, Http.utf8.take(t, Nat.sub(
            Nat.add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t)),
            Http.utf8.width(Char.to_u32(h))))}),
          Nat.is_lt(Nat.add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t)),
            Http.utf8.width(Char.to_u32(h))),
          False{},
          lt_add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t))),
        Equal.trans(String,
          SCon{h, Http.utf8.take(t, Nat.sub(
            Nat.add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t)),
            Http.utf8.width(Char.to_u32(h))))},
          SCon{h, Http.utf8.take(t, Http.utf8.len(t))},
          SCon{h, t},
          Equal.cong(Nat, String, m => SCon{h, Http.utf8.take(t, m)},
            Nat.sub(Nat.add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t)),
              Http.utf8.width(Char.to_u32(h))),
            Http.utf8.len(t),
            sub_add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t))),
          Equal.cong(String, String, x => SCon{h, x},
            Http.utf8.take(t, Http.utf8.len(t)), t, take_all(t))))

def Laws.clen_exact(st, body):
  Equal.trans(Http.Reply,
    Http.parse.clen(st, Http.utf8.len(body), body),
    Http.parse.short(st, Http.utf8.len(body), body, False{}),
    Http.Reply{st, body},
    Equal.cong(Bool, Http.Reply,
      b => Http.parse.short(st, Http.utf8.len(body), body, b),
      Nat.is_lt(Http.utf8.len(body), Http.utf8.len(body)), False{},
      lt_self(Http.utf8.len(body))),
    Equal.cong(String, Http.Reply, x => Http.Reply{st, x},
      Http.utf8.take(body, Http.utf8.len(body)), body, take_all(body)))

# LAW: every string starts with nothing
law starts_nil:
  for s: String
  {String.starts_with(s, SNil{}) == True{} : Bool}

def starts_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def Laws.path_absolute(ps):
  match ps:
    case []:
      {==}
    case h <> t:
      starts_nil(String.join(t, "/"))
