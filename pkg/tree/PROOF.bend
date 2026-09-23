# pkg/tree: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./tree.bend as T
import ../pkg.bend as K
import ../path.bend as P
import ../../sha/sha.bend as Sha
import ./LAWS.bend as Laws

# LAW: the first step of a walk whose entry the checkout does not hold stops
# on the entry, with nothing found and nothing queued
law first_step_stops:
  for +eb: String
  for +entry: String
  for +fs: List<&2, T.Source>
  for miss: {None{} == T.look(fs, entry) : Maybe<&2, String>}
  {T.step(fs, eb, T.State{[], [], "", [K.Task{entry, ""}]})
    == T.State{[], [], entry, []} : T.State}

def first_step_stops(eb, entry, fs, miss):
  %miss : {T.visit.have(_, fs, entry, "", eb, [], [], "", [])
    == T.State{[], [], entry, []} : T.State}
  {==}

# LAW: a walk that has stopped stays stopped, whatever fuel is left
law stopped_stays:
  for f: Nat
  for +eb: String
  for +entry: String
  for +fs: List<&2, T.Source>
  {T.walk(f, fs, eb, T.State{[], [], entry, []})
    == T.State{[], [], entry, []} : T.State}

def stopped_stays(f, _eb, _entry, _fs):
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# LAW: so the whole walk ends where the first step stopped
law walk_stops:
  for f: Nat
  for +entry: String
  for +fs: List<&2, T.Source>
  for miss: {None{} == T.look(fs, entry) : Maybe<&2, String>}
  {T.walk((1n + f : Nat), fs, P.base(entry), T.State{[], [], "", [K.Task{entry, ""}]})
    == T.State{[], [], entry, []} : T.State}

def walk_stops(f, entry, fs, miss):
  Equal.trans(T.State,
    T.walk(f, fs, P.base(entry),
      T.step(fs, P.base(entry), T.State{[], [], "", [K.Task{entry, ""}]})),
    T.walk(f, fs, P.base(entry), T.State{[], [], entry, []}),
    T.State{[], [], entry, []},
    Equal.cong(T.State, T.State, s => T.walk(f, fs, P.base(entry), s),
      T.step(fs, P.base(entry), T.State{[], [], "", [K.Task{entry, ""}]}),
      T.State{[], [], entry, []},
      first_step_stops(P.base(entry), entry, fs, miss)),
    stopped_stays(f, P.base(entry), entry, fs))

# LAW: a walk that stopped on a named file is refused, naming it
law made_stopped:
  for +entry: String
  for ne: {False{} == String.is_empty(entry) : Bool}
  {T.made(entry, T.State{[], [], entry, []})
    == T.Refused{"ez: " ++ entry ++ " is imported but not there"} : T.Walked}

def made_stopped(entry, ne):
  %ne : {T.made.go(Bool.not(_), entry, P.dir(entry), [])
    == T.Refused{"ez: " ++ entry ++ " is imported but not there"} : T.Walked}
  {==}

def Laws.absent_entry_refused(f, entry, fs, ne, miss):
  Equal.trans(T.Walked,
    T.made(entry, T.walk((1n + f : Nat), fs, P.base(entry),
      T.State{[], [], "", [K.Task{entry, ""}]})),
    T.made(entry, T.State{[], [], entry, []}),
    T.Refused{"ez: " ++ entry ++ " is imported but not there"},
    Equal.cong(T.State, T.Walked, s => T.made(entry, s),
      T.walk((1n + f : Nat), fs, P.base(entry), T.State{[], [], "", [K.Task{entry, ""}]}),
      T.State{[], [], entry, []},
      walk_stops(f, entry, fs, miss)),
    made_stopped(entry, ne))

# LAW: placing found files and weighing laid ones give the same file list:
# each is the found name under the root, with the sha256 of the found text
law placed_is_laid:
  for +pre: String
  for +out: List<&2, T.Found>
  {K.placed(pre, T.found.sums(out)) == T.sums(T.laid(pre, out)) : List<&2, K.File>}

def placed_is_laid(pre, out):
  match out:
    case []:
      {==}
    case T.Found{+raw, +text} <> t:
      Equal.cong(List<&2, K.File>, List<&2, K.File>,
        xs => K.File{P.join(pre, raw), Sha.hex(text)} <> xs,
        K.placed(pre, T.found.sums(t)), T.sums(T.laid(pre, t)),
        placed_is_laid(pre, t))

def Laws.walked_named_by_texts(pre, out):
  Equal.cong(List<&2, K.File>, String, fs => K.hash_of(fs),
    K.placed(pre, T.found.sums(out)), T.sums(T.laid(pre, out)),
    placed_is_laid(pre, out))

def Laws.walked_manifest_of_texts(pre, out):
  Equal.cong(List<&2, K.File>, String, fs => K.manifest_of(fs),
    K.placed(pre, T.found.sums(out)), T.sums(T.laid(pre, out)),
    placed_is_laid(pre, out))
