# net: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./http.bend as Http
import ./url.bend as Url
import ./LAWS.bend as Laws
import ../check/eq.bend as Eq

# LAW: one step of the partition, with the branch the step takes given as a
# parameter, since a match may not scrutinise a computed value
law utf8_split.arm:
  for -h: Char
  for -t: String
  for -m: Nat
  for b: Bool
  for ih: {String.append(Http.utf8.take(t, m), Http.utf8.drop(t, m)) == t : String}
  {String.append(
    Http.utf8.take.step(b, h, _u => Http.utf8.take(t, m)),
    Http.utf8.drop.step(b, h, t, _u => Http.utf8.drop(t, m))) == SCon{h, t} : String}

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
          b => Http.utf8.take.step(b, h, _u => Http.utf8.take(t, Nat.sub(
            Nat.add(Http.utf8.width(Char.to_u32(h)), Http.utf8.len(t)),
            Http.utf8.width(Char.to_u32(h))))),
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

# The rewrite of net/http.bend's chunked decode, proved to have changed only
# what the decode costs. LAWS.bend keeps the definitions as they were; what
# follows is that each new one answers what the old one answered.
#
# All four step laws have the same shape, because the four defects had the
# same shape: a recursive call sitting in an arm of a `Bool.pick`, which is an
# ordinary function and so builds both arms before it picks. The new code
# hands the recursion in as a thunk and applies it only in the arm that wants
# it. A `Bool.pick` and a thunked step agree arm for arm, which is what each
# `.arm` law says, and induction on the string carries it.

# LAW: one step of the take, with the branch given as a parameter, since a
# match may not scrutinise a computed value
law take_agrees.arm:
  for -h: Char
  for -t: String
  for -m: Nat
  for b: Bool
  for ih: {Laws.old.take(t, m) == Http.utf8.take(t, m) : String}
  {Bool.pick(String, b, SNil{}, SCon{h, Laws.old.take(t, m)})
    == Http.utf8.take.step(b, h, _u => Http.utf8.take(t, m)) : String}

def take_agrees.arm(h, t, m, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(String, String, x => SCon{h, x},
        Laws.old.take(t, m), Http.utf8.take(t, m), ih)

def Laws.take_agrees(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      take_agrees.arm(h, t, Nat.sub(n, Http.utf8.width(Char.to_u32(h))),
        Nat.is_lt(n, Http.utf8.width(Char.to_u32(h))),
        Laws.take_agrees(t, Nat.sub(n, Http.utf8.width(Char.to_u32(h)))))

# LAW: one step of the drop
law drop_agrees.arm:
  for -h: Char
  for -t: String
  for -m: Nat
  for b: Bool
  for ih: {Laws.old.drop(t, m) == Http.utf8.drop(t, m) : String}
  {Bool.pick(String, b, SCon{h, t}, Laws.old.drop(t, m))
    == Http.utf8.drop.step(b, h, t, _u => Http.utf8.drop(t, m)) : String}

def drop_agrees.arm(_h, _t, _m, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.drop_agrees(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      drop_agrees.arm(h, t, Nat.sub(n, Http.utf8.width(Char.to_u32(h))),
        Nat.is_lt(n, Http.utf8.width(Char.to_u32(h))),
        Laws.drop_agrees(t, Nat.sub(n, Http.utf8.width(Char.to_u32(h)))))

# LAW: one step of the walk
law divide_agrees.arm:
  for -h: Char
  for -t: String
  for -pat: String
  for -n: Nat
  for b: Bool
  for ih: {Laws.old.divide.go(t, pat, n) == Http.divide.go(t, pat, n) : Http.Cut}
  {Bool.pick(Http.Cut, b, Http.Cut{"", String.drop(SCon{h, t}, n)},
    Http.divide.push(h, Laws.old.divide.go(t, pat, n)))
    == Http.divide.step(b, h, t, n, _u => Http.divide.go(t, pat, n)) : Http.Cut}

def divide_agrees.arm(h, t, pat, n, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Http.Cut, Http.Cut, r => Http.divide.push(h, r),
        Laws.old.divide.go(t, pat, n), Http.divide.go(t, pat, n), ih)

# LAW: the walk agrees, at whatever pattern length the divide hands it
law divide_agrees.go:
  for s: String
  for +pat: String
  for +n: Nat
  {Laws.old.divide.go(s, pat, n) == Http.divide.go(s, pat, n) : Http.Cut}

def divide_agrees.go(s, pat, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      divide_agrees.arm(h, t, pat, n,
        String.starts_with(SCon{h, t}, pat),
        divide_agrees.go(t, pat, n))

def Laws.divide_agrees(s, pat):
  divide_agrees.go(s, pat, String.length(pat))

# LAW: one step of the hex read
law hex_agrees.arm:
  for -t: String
  for -acc: Nat
  for -v: U32
  for b: Bool
  for ih: {Laws.old.hex.go(t, Nat.add(Nat.mul(acc, 16n), U32.to_nat(v)))
    == Http.hex.go(t, Nat.add(Nat.mul(acc, 16n), U32.to_nat(v))) : Nat}
  {Bool.pick(Nat, b, acc,
    Laws.old.hex.go(t, Nat.add(Nat.mul(acc, 16n), U32.to_nat(v))))
    == Http.hex.step(b, acc,
      _u => Http.hex.go(t, Nat.add(Nat.mul(acc, 16n), U32.to_nat(v)))) : Nat}

def hex_agrees.arm(_t, _acc, _v, b, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.hex_agrees(s, acc):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      hex_agrees.arm(t, acc, Http.hex.val(h),
        U32.is_ge(Http.hex.val(h), 16),
        Laws.hex_agrees(t, Nat.add(Nat.mul(acc, 16n),
          U32.to_nat(Http.hex.val(h)))))

# LAW: nothing appended to a string leaves the string
law append_nil:
  for s: String
  {String.append(s, SNil{}) == s : String}

def append_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(t, SNil{}), t, append_nil(t))

# LAW: where the brackets fall in a run of appends does not change the run.
# This is what lets the chunk loop drop its accumulator: appending each chunk
# onto what came before it and appending each chunk onto what comes after it
# give the same string, and only the second is linear in the body.
law append_assoc:
  for a: String
  for b: String
  for c: String
  {String.append(String.append(a, b), c)
    == String.append(a, String.append(b, c)) : String}

def append_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(String.append(t, b), c),
        String.append(t, String.append(b, c)),
        append_assoc(t, b, c))

# LAW: the loop with an accumulator is the loop without one, with whatever the
# accumulator held in front of it. The law is stated for every accumulator and
# not only the empty one, because that is what the induction needs: one pass
# puts a chunk into the accumulator before the next pass sees it.
law chunks_agrees:
  for +fuel: Nat
  for +c: Http.Cut
  for +acc: String
  {Laws.old.chunks(fuel, c, acc)
    == String.append(acc, Http.chunks(fuel, c)) : String}

def chunks_agrees(fuel, c, acc):
  match fuel c:
    case 0n _:
      Equal.sym(String, String.append(acc, SNil{}), acc, append_nil(acc))
    case 1n+f Http.NoCut{}:
      Equal.sym(String, String.append(acc, SNil{}), acc, append_nil(acc))
    case 1n+f Http.Cut{before, +after}:
      Equal.trans(String,
        Laws.old.chunks(f,
          Http.divide(Http.utf8.drop(after,
            Nat.add(Http.hexlen(before), 2n)), "\r\n"),
          String.append(acc, Http.utf8.take(after, Http.hexlen(before)))),
        String.append(
          String.append(acc, Http.utf8.take(after, Http.hexlen(before))),
          Http.chunks(f, Http.divide(Http.utf8.drop(after,
            Nat.add(Http.hexlen(before), 2n)), "\r\n"))),
        String.append(acc,
          String.append(Http.utf8.take(after, Http.hexlen(before)),
            Http.chunks(f, Http.divide(Http.utf8.drop(after,
              Nat.add(Http.hexlen(before), 2n)), "\r\n")))),
        chunks_agrees(f,
          Http.divide(Http.utf8.drop(after,
            Nat.add(Http.hexlen(before), 2n)), "\r\n"),
          String.append(acc, Http.utf8.take(after, Http.hexlen(before)))),
        append_assoc(acc, Http.utf8.take(after, Http.hexlen(before)),
          Http.chunks(f, Http.divide(Http.utf8.drop(after,
            Nat.add(Http.hexlen(before), 2n)), "\r\n"))))

def Laws.dechunk_agrees(s):
  chunks_agrees(String.length(s), Http.divide(s, "\r\n"), SNil{})

# The rest of the text begins here. Every one of these laws is either a split
# walked one character at a time, or a hypothesis rewritten into the one place
# the code branches. The boolean facts each of them ends on -- that an `and`
# answering True says both halves did, that a bit is not the other bit -- are
# in check/eq.bend beside the other Base facts Base does not state.

# LAW: one character of the split, with the separator test given as a
# parameter, since a match may not scrutinise a computed value
law split_whole.step:
  for +h: Char
  for +t: String
  for +c: Char
  for e: {False{} == Char.is_eq(h, c) : Bool}
  for ih: {String.split(t, c) == [t] : List<&2, String>}
  {String.split(SCon{h, t}, c) == [SCon{h, t}] : List<&2, String>}

def split_whole.step(h, t, c, e, ih):
  %e : {String.split.fin(h, String.split(t, c), _) == [SCon{h, t}]
    : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>,
    r => String.split.fin(h, r, False{}),
    String.split(t, c), [t], ih)

def Laws.split_whole(s, c, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      split_whole.step(h, t, c,
        Equal.sym(Bool, Char.is_eq(h, c), False{},
          Eq.not.true(Char.is_eq(h, c),
            Eq.and.left(Bool.not(Char.is_eq(h, c)), Laws.avoids(t, c), e))),
        Laws.split_whole(t, c,
          Eq.and.right(Bool.not(Char.is_eq(h, c)), Laws.avoids(t, c), e)))

# LAW: one character before the cut, the same shape as the step above
law split_cut.step:
  for +h: Char
  for +t: String
  for +c: Char
  for r: String
  for e: {False{} == Char.is_eq(h, c) : Bool}
  for ih: {String.split(String.append(t, SCon{c, r}), c) == t <> String.split(r, c)
    : List<&2, String>}
  {String.split(String.append(SCon{h, t}, SCon{c, r}), c)
    == SCon{h, t} <> String.split(r, c) : List<&2, String>}

def split_cut.step(h, t, c, r, e, ih):
  %e : {String.split.fin(h, String.split(String.append(t, SCon{c, r}), c), _)
    == SCon{h, t} <> String.split(r, c) : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>,
    x => String.split.fin(h, x, False{}),
    String.split(String.append(t, SCon{c, r}), c), t <> String.split(r, c), ih)

# By induction on what comes before the cut. The character itself cuts, which
# is the one place the separator is compared with itself.
def Laws.split_cut(s, c, r, e):
  match s:
    case SNil{}:
      Equal.cong(Bool, List<&2, String>,
        x => String.split.fin(c, String.split(r, c), x),
        Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
    case SCon{+h, +t}:
      split_cut.step(h, t, c, r,
        Equal.sym(Bool, Char.is_eq(h, c), False{},
          Eq.not.true(Char.is_eq(h, c),
            Eq.and.left(Bool.not(Char.is_eq(h, c)), Laws.avoids(t, c), e))),
        Laws.split_cut(t, c, r,
          Eq.and.right(Bool.not(Char.is_eq(h, c)), Laws.avoids(t, c), e)))

# Both sides of the header law read the same first piece: with the extension
# the cut gives it, without the extension the whole split is it.
def Laws.hexlen_ignores_extension(s, ext, e):
  Equal.trans(Nat,
    Http.hexlen(String.append(s, SCon{';', ext})),
    Http.hex.go(String.trim(s), 0n),
    Http.hexlen(s),
    Equal.cong(List<&2, String>, Nat,
      ps => Http.hex.go(String.trim(Http.first(ps)), 0n),
      String.split(String.append(s, SCon{';', ext}), ';'),
      s <> String.split(ext, ';'),
      Laws.split_cut(s, ';', ext, e)),
    Equal.sym(Nat, Http.hexlen(s), Http.hex.go(String.trim(s), 0n),
      Equal.cong(List<&2, String>, Nat,
        ps => Http.hex.go(String.trim(Http.first(ps)), 0n),
        String.split(s, ';'), [s], Laws.split_whole(s, ';', e))))

# The first piece of the cut is the word, and the second is the head of what
# the rest split into, which is `first` of it.
def Laws.first_is_first_word(w, r, e):
  Equal.cong(List<&2, String>, String, ps => Http.first(ps),
    String.split(String.append(w, SCon{' ', r}), ' '),
    w <> String.split(r, ' '), Laws.split_cut(w, ' ', r, e))

def Laws.second_is_next_word(w, r, e):
  Equal.cong(List<&2, String>, String, ps => Http.second(ps),
    String.split(String.append(w, SCon{' ', r}), ' '),
    w <> String.split(r, ' '), Laws.split_cut(w, ' ', r, e))

# The method and its space are four literal characters, so the comparison
# computes down to the path against itself, and the headers after it are what
# is appended.
def Laws.request_names_path(host, path):
  Eq.starts_append(path,
    " HTTP/1.1\r\n" ++ "Host: " ++ host ++ "\r\n" ++ "User-Agent: ez\r\n"
      ++ "Accept: */*\r\n" ++ "Connection: close\r\n\r\n")

# The two verdicts of the head cut, each rewritten into the one place `parse`
# branches on it.
def Laws.parse_needs_blank_line(_raw, e):
  %e : {Http.parse.cut(_)
    == Http.Torn{"the response head has no blank line after it"}
    : Http.Reply}
  {==}

def Laws.parse_splits_at_blank_line(_raw, before, after, e):
  %e : {Http.parse.cut(_) == Http.parse.head(String.lines(before), after)
    : Http.Reply}
  {==}

# `torn ` and `bad ` are literals, so each comparison computes down to the
# reason against the empty prefix; a status or a scheme is not, so each of
# those is the append law.
def Laws.show_torn_is_marked(why):
  Eq.starts_nil(why)

def Laws.show_reply_opens_with_status(status, body):
  Eq.starts_append(U32.show(status), " " ++ body)

def Laws.url_show_bad_is_marked(why):
  Eq.starts_nil(why)

def Laws.url_show_opens_with_scheme(scheme, host, port, path):
  Eq.starts_append(scheme, " " ++ host ++ " " ++ U32.show(port) ++ " " ++ path)

# The port a scheme implies is one test, and the hypothesis answers it.
def Laws.dflt_plain(_scheme, e):
  %e : {Bool.pick(U32, _, 443, 80) == 80 : U32}
  {==}

# The scheme cut is one match on the split, and the hypothesis says which arm.
def Laws.parse_scheme_first(_url, h, t, e):
  %e : {Url.parse.scheme(_)
    == Url.parse.rest(String.to_lower(h), String.join(t, ":")) : Url.Loc}
  {==}
