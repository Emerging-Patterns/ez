# proofs of laws/EscapingImportRefused.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/EscapingImportRefused.bend as Laws

# LAW: a step whose next file is new and above the checkout's top stops the
# walk on it, naming the import, and reads nothing
law escape_step:
  for +tree: K.Tree
  for +eb: String
  for +seen: List<&2, String>
  for +out: List<&2, K.Hit>
  for +file: String
  for +ns: String
  for +rest: List<&2, K.Task>
  for fresh: {False{} == K.seen.has(seen, file) : Bool}
  for up: {True{} == K.outside(file) : Bool}
  {K.step(tree, eb, K.State{seen, out, K.Going{}, K.Task{file, ns} <> rest})
    == K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest} : K.State}

def escape_step(tree, eb, seen, out, file, ns, rest, fresh, up):
  %fresh : {K.visit.go(_, tree, file, ns, eb, seen, out, rest)
    == K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest} : K.State}
  %up : {K.visit.in(_, tree, file, ns, eb, seen, out, rest)
    == K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest} : K.State}
  {==}

# LAW: a walk that has stopped on a climb stays stopped, whatever fuel is
# left and whatever is still queued
law climbed_stays:
  for f: Nat
  for +tree: K.Tree
  for +eb: String
  for +seen: List<&2, String>
  for +out: List<&2, K.Hit>
  for +at: String
  for +rest: List<&2, K.Task>
  {K.walk(f, tree, eb, K.State{seen, out, K.Climbs{at}, rest})
    == K.State{seen, out, K.Climbs{at}, rest} : K.State}

def climbed_stays(f, _tree, _eb, _seen, _out, _at, rest):
  match f rest:
    case 0n Nil{}:
      {==}
    case 0n Con{_h, _t}:
      {==}
    case 1n+g Nil{}:
      {==}
    case 1n+g Con{_h, _t}:
      {==}

def Laws.escaping_import_refused(f, entry, tree, eb, seen, out, file, ns, rest, fresh, up):
  Equal.cong(K.State, K.Walked, s => K.made(entry, s),
    K.walk((1n + f : Nat), tree, eb,
      K.State{seen, out, K.Going{}, K.Task{file, ns} <> rest}),
    K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest},
    Equal.trans(K.State,
      K.walk(f, tree, eb,
        K.step(tree, eb, K.State{seen, out, K.Going{}, K.Task{file, ns} <> rest})),
      K.walk(f, tree, eb, K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest}),
      K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest},
      Equal.cong(K.State, K.State, s => K.walk(f, tree, eb, s),
        K.step(tree, eb, K.State{seen, out, K.Going{}, K.Task{file, ns} <> rest}),
        K.State{seen, out, K.Climbs{K.climbs.name(ns, file)}, rest},
        escape_step(tree, eb, seen, out, file, ns, rest, fresh, up)),
      climbed_stays(f, tree, eb, seen, out, K.climbs.name(ns, file), rest)))
