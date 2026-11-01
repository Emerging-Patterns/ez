# proofs of laws/DirPlain.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/path.bend as Path
import ../laws/CompName.bend as L1
import ../laws/DirPlain.bend as Laws
import ../laws/defs/Slashless.bend as D1
import ./lemmas/LockPlannerFacts.bend as M1

# LAW: one character before a slash
law split_slash.step:
  for +h: Char
  for +t: String
  for +r: String
  for e: {False{} == Char.is_eq(h, '/') : Bool}
  for ih: {String.split(String.append(t, SCon{'/', r}), '/')
    == t <> String.split(r, '/') : List<&2, String>}
  {String.split(String.append(SCon{h, t}, SCon{'/', r}), '/')
    == SCon{h, t} <> String.split(r, '/') : List<&2, String>}

def split_slash.step(h, t, r, e, ih):
  %e : {String.split.fin(h, String.split(String.append(t, SCon{'/', r}), '/'), _)
    == SCon{h, t} <> String.split(r, '/') : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>,
    x => String.split.fin(h, x, False{}),
    String.split(String.append(t, SCon{'/', r}), '/'),
    t <> String.split(r, '/'), ih)

# LAW: a slashless prefix splits off at the first `/`
law split_slash:
  for +p: String
  for +r: String
  for +e: {D1.slashless(p) == True{} : Bool}
  {String.split(String.append(p, SCon{'/', r}), '/')
    == p <> String.split(r, '/') : List<&2, String>}

def split_slash(p, r, e):
  match p:
    case SNil{}:
      Equal.cong(Bool, List<&2, String>,
        x => String.split.fin('/', String.split(r, '/'), x),
        Char.is_eq('/', '/'), True{}, Eq.char_eq_self('/'))
    case SCon{+h, +t}:
      split_slash.step(h, t, r,
        Equal.sym(Bool, Char.is_eq(h, '/'), False{},
          Eq.not.true(Char.is_eq(h, '/'),
            Eq.and.left(Bool.not(Char.is_eq(h, '/')), D1.slashless(t), e))),
        split_slash(t, r,
          Eq.and.right(Bool.not(Char.is_eq(h, '/')), D1.slashless(t), e)))

# LAW: a slashless non-empty path does not begin at the root, and appending
# to it leaves that first character where it was
law slashless_rel:
  for +p: String
  for +x: String
  for +e: {D1.slashless(p) == True{} : Bool}
  for e0: {False{} == String.is_empty(p) : Bool}
  {False{} == String.starts_with(String.append(p, x), "/") : Bool}

def slashless_rel(p, x, e, e0):
  match p:
    case SNil{}:
      Eq.bit.absurd(&2,
        {False{} == String.starts_with(String.append(SNil{}, x), "/") : Bool},
        e0)
    case SCon{+h, +t}:
      Equal.sym(Bool,
        String.starts_with.go.if("", String.append(t, x), Char.is_eq(h, '/')),
        False{},
        Equal.trans(Bool,
          String.starts_with.go.if("", String.append(t, x), Char.is_eq(h, '/')),
          String.starts_with.go.if("", String.append(t, x), False{}),
          False{},
          Equal.cong(Bool, Bool,
            b => String.starts_with.go.if("", String.append(t, x), b),
            Char.is_eq(h, '/'), False{},
            Eq.not.true(Char.is_eq(h, '/'),
              Eq.and.left(Bool.not(Char.is_eq(h, '/')), D1.slashless(t), e))),
          {==}))

# LAW: a name followed by a climb, from an empty relative walk, cancels
law walk_name_up:
  for +p: String
  for e0: {False{} == String.is_empty(p) : Bool}
  for e1: {False{} == String.eq(p, ".") : Bool}
  for +e2: {False{} == String.eq(p, "..") : Bool}
  {Path.norm.walk([p, ".."], Path.Walk{False{}, []})
    == Path.Walk{False{}, []} : Path.Walk}

# LAW: a climb off a kept name, once the name is known not to be a climb
law walk_name_up.fin:
  for +p: String
  for e2: {False{} == String.eq(p, "..") : Bool}
  {Path.norm.walk([".."], Path.Walk{False{}, p <> []})
    == Path.Walk{False{}, []} : Path.Walk}

def walk_name_up.fin(p, e2):
  %e2 : {Path.Walk{False{}, Path.up.back(_, p, [])}
    == Path.Walk{False{}, []} : Path.Walk}
  {==}

def walk_name_up(p, e0, e1, e2):
  Equal.trans(Path.Walk,
    Path.norm.walk([".."], Path.norm.go(Path.Walk{False{}, []}, Path.comp_of(p))),
    Path.norm.walk([".."], Path.norm.go(Path.Walk{False{}, []}, Path.CName{p})),
    Path.Walk{False{}, []},
    Equal.cong(Path.Comp, Path.Walk,
      c => Path.norm.walk([".."], Path.norm.go(Path.Walk{False{}, []}, c)),
      Path.comp_of(p), Path.CName{p}, L1.comp_name(p, e0, e1, e2)),
    walk_name_up.fin(p, e2))

def Laws.dir_plain(p, e, e0, e1, e2):
  Equal.trans(String,
    Path.norm.fin(Path.norm.walk(String.split(String.append(p, "/.."), '/'),
      Path.Walk{String.starts_with(String.append(p, "/.."), "/"), []})),
    Path.norm.fin(Path.norm.walk(p <> String.split("..", '/'),
      Path.Walk{False{}, []})),
    ".",
    Equal.trans(String,
      Path.norm.fin(Path.norm.walk(String.split(String.append(p, "/.."), '/'),
        Path.Walk{String.starts_with(String.append(p, "/.."), "/"), []})),
      Path.norm.fin(Path.norm.walk(String.split(String.append(p, "/.."), '/'),
        Path.Walk{False{}, []})),
      Path.norm.fin(Path.norm.walk(p <> String.split("..", '/'),
        Path.Walk{False{}, []})),
      Equal.cong(Bool, String,
        abs => Path.norm.fin(Path.norm.walk(
          String.split(String.append(p, "/.."), '/'), Path.Walk{abs, []})),
        String.starts_with(String.append(p, "/.."), "/"), False{},
        Equal.sym(Bool, False{},
          String.starts_with(String.append(p, "/.."), "/"),
          slashless_rel(p, "/..", e, e0))),
      Equal.cong(List<&2, String>, String,
        cs => Path.norm.fin(Path.norm.walk(cs, Path.Walk{False{}, []})),
        String.split(String.append(p, "/.."), '/'),
        p <> String.split("..", '/'), split_slash(p, "..", e))),
    Equal.trans(String,
      Path.norm.fin(Path.norm.walk(p <> [".."], Path.Walk{False{}, []})),
      Path.norm.fin(Path.Walk{False{}, []}),
      ".",
      Equal.cong(Path.Walk, String, st => Path.norm.fin(st),
        Path.norm.walk([p, ".."], Path.Walk{False{}, []}),
        Path.Walk{False{}, []}, walk_name_up(p, e0, e1, e2)),
      {==}))
