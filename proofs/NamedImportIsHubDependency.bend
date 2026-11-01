# proofs of laws/NamedImportIsHubDependency.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../laws/NamedImportIsHubDependency.bend as Laws
import ../laws/defs/LicenseGiven.bend as D1

# ---------------------------------------------------------------------------
# named hub imports (laws/NamedImportIsHubDependency.bend)

# LAW: an `or` with True on the right picks the first arm
law or_true_pick:
  for a: Bool
  for +xs: List<&2, K.Task>
  {Bool.pick(List<&2, K.Task>, Bool.or(a, True{}), [], xs) == [] : List<&2, K.Task>}

def or_true_pick(a, _xs):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.named_is_no_module(dir, nd, spec, e):
  %e : {Bool.pick(List<&2, K.Task>, Bool.or(K.is_hub(spec), _), [],
    [K.Task{Path.join(dir, spec), Path.unbend(Path.join(nd, spec))}]) == [] : List<&2, K.Task>}
  or_true_pick(K.is_hub(spec), [K.Task{Path.join(dir, spec), Path.unbend(Path.join(nd, spec))}])

# LAW: the walk stops at a name the hub rules out, whatever it was given of
# the LICENSE, so long as it was given it
law unnamed_at:
  for l: K.Look
  for +tree: K.Tree
  for +text: String
  for +file: String
  for +ns: String
  for eb: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for rest: List<&2, K.Task>
  for g: {True{} == D1.given(l) : Bool}
  for n: {False{} == String.is_empty(K.unnamed(K.scan.mods(K.scan(text)))) : Bool}
  {K.visit.put(K.asked(l, K.beside(file),
      _u => K.named.check(K.unnamed(K.scan.mods(K.scan(text))),
        _v => K.foreign.check(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(K.scan(text))))),
      tree, K.scan(text), text, file, ns, eb, seen, out, rest)
    == K.State{seen, out, K.Unnamed{K.unnamed(K.scan.mods(K.scan(text)))}, K.Task{file, ns} <> rest}
    : K.State}

def unnamed_at(l, tree, text, file, ns, eb, seen, out, rest, g, n):
  match l:
    case K.Here{_x}:
      %n : {K.visit.put(K.named.check.at(_, K.unnamed(K.scan.mods(K.scan(text))),
          _v => K.foreign.check(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(K.scan(text)))),
        tree, K.scan(text), text, file, ns, eb, seen, out, rest)
        == K.State{seen, out, K.Unnamed{K.unnamed(K.scan.mods(K.scan(text)))}, K.Task{file, ns} <> rest}
        : K.State}
      {==}
    case K.Absent{}:
      %n : {K.visit.put(K.named.check.at(_, K.unnamed(K.scan.mods(K.scan(text))),
          _v => K.foreign.check(tree, Path.dir(file), K.nsdir(ns), K.scan.foreign(K.scan(text)))),
        tree, K.scan(text), text, file, ns, eb, seen, out, rest)
        == K.State{seen, out, K.Unnamed{K.unnamed(K.scan.mods(K.scan(text)))}, K.Task{file, ns} <> rest}
        : K.State}
      {==}
    case K.Unasked{}:
      Eq.bit.absurd2(&2, {K.visit.put(K.Asking{K.beside(file)}, tree, K.scan(text), text, file, ns,
        eb, seen, out, rest)
        == K.State{seen, out, K.Unnamed{K.unnamed(K.scan.mods(K.scan(text)))}, K.Task{file, ns} <> rest}
        : K.State}, g)

def Laws.unnamed_stops(tree, text, file, ns, eb, seen, out, rest, g, n):
  unnamed_at(K.find(tree, K.beside(file)), tree, text, file, ns, eb, seen, out, rest, g, n)

def Laws.unnamed_refused(_entry, _nv, _out):
  {==}

# ---------------------------------------------------------------------------
# named hub imports (EZ-HUB)

def Laws.lock_reads_named(spec, e):
  %e : {Bool.pick(List<&2, String>, _, [], [K.named.of(spec)]) == [K.named.of(spec)]
    : List<&2, String>}
  {==}
