# proofs of laws/NormDot.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/path.bend as Path
import ../src/add/world.bend as A
import ../laws/NormDot.bend as Laws
import ../laws/SkipId.bend as L1
import ./lemmas/PlanEffectFacts.bend as M1

# LAW: `./` plus a path splits into a skip and whatever the path splits into
law split_dot:
  for p: String
  {String.split(SCon{'.', SCon{'/', p}}, '/') == "." <> String.split(p, '/')
    : List<&2, String>}

def split_dot(p):
  Equal.trans(List<&2, String>,
    String.split.fin('.', String.split(SCon{'/', p}, '/'), Char.is_eq('.', '/')),
    String.split.fin('.', String.split(SCon{'/', p}, '/'), False{}),
    "." <> String.split(p, '/'),
    Equal.cong(Bool, List<&2, String>,
      x => String.split.fin('.', String.split(SCon{'/', p}, '/'), x),
      Char.is_eq('.', '/'), False{}, {==}),
    Equal.cong(List<&2, String>, List<&2, String>,
      r => String.split.fin('.', r, False{}),
      String.split(SCon{'/', p}, '/'), SNil{} <> String.split(p, '/'),
      Equal.cong(Bool, List<&2, String>,
        x => String.split.fin('/', String.split(p, '/'), x),
        Char.is_eq('/', '/'), True{}, Eq.char_eq_self('/'))))

# LAW: walking a skip first is walking what follows
# a `.` is not a component: the walk skips it. A lemma of `walk_skip_dot`
# below, stated here rather than in a law file because it is one computed case
# and no requirement's claim.
law comp_dot:
  {Path.comp_of(".") == Path.CSkip{} : Path.Comp}

def comp_dot():
  {==}

law walk_skip_dot:
  for cs: List<&2, String>
  for w: Path.Walk
  {Path.norm.walk("." <> cs, w) == Path.norm.walk(cs, w) : Path.Walk}

def walk_skip_dot(cs, w):
  Equal.trans(Path.Walk,
    Path.norm.walk(cs, Path.norm.go(w, Path.comp_of("."))),
    Path.norm.walk(cs, Path.norm.go(w, Path.CSkip{})),
    Path.norm.walk(cs, w),
    Equal.cong(Path.Comp, Path.Walk,
      c => Path.norm.walk(cs, Path.norm.go(w, c)),
      Path.comp_of("."), Path.CSkip{}, comp_dot()),
    Equal.cong(Path.Walk, Path.Walk,
      st => Path.norm.walk(cs, st),
      Path.norm.go(w, Path.CSkip{}), w, L1.skip_id(w)))

def Laws.norm_dot(p, e):
  Equal.trans(String,
    Path.norm.fin(Path.norm.walk(String.split(SCon{'.', SCon{'/', p}}, '/'),
      Path.Walk{String.starts_with(SCon{'.', SCon{'/', p}}, "/"), []})),
    Path.norm.fin(Path.norm.walk(String.split(p, '/'), Path.Walk{False{}, []})),
    Path.norm.fin(Path.norm.walk(String.split(p, '/'),
      Path.Walk{String.starts_with(p, "/"), []})),
    Equal.trans(String,
      Path.norm.fin(Path.norm.walk(String.split(SCon{'.', SCon{'/', p}}, '/'),
        Path.Walk{False{}, []})),
      Path.norm.fin(Path.norm.walk("." <> String.split(p, '/'),
        Path.Walk{False{}, []})),
      Path.norm.fin(Path.norm.walk(String.split(p, '/'),
        Path.Walk{False{}, []})),
      Equal.cong(List<&2, String>, String,
        cs => Path.norm.fin(Path.norm.walk(cs, Path.Walk{False{}, []})),
        String.split(SCon{'.', SCon{'/', p}}, '/'),
        "." <> String.split(p, '/'), split_dot(p)),
      Equal.cong(Path.Walk, String,
        st => Path.norm.fin(st),
        Path.norm.walk("." <> String.split(p, '/'), Path.Walk{False{}, []}),
        Path.norm.walk(String.split(p, '/'), Path.Walk{False{}, []}),
        walk_skip_dot(String.split(p, '/'), Path.Walk{False{}, []}))),
    Equal.cong(Bool, String,
      abs => Path.norm.fin(Path.norm.walk(String.split(p, '/'),
        Path.Walk{abs, []})),
      False{}, String.starts_with(p, "/"), e))
