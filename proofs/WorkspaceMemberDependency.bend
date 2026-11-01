# proofs of laws/WorkspaceMemberDependency.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/pub/plan.bend as PP
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../laws/WorkspaceMemberDependency.bend as Laws

# ---------------------------------------------------------------------------
# the values a table's pairs give back

# The values a table's pairs give back. A source or a tool is written as a
# run of pairs with distinct keys, a pair left out when its value is empty.
# A lookup reads such a run as it reads the run with every pair written,
# empty values included, and over that run a lookup for a key the text names
# computes.

# the run of pairs keys and values are written as, a pair left out when its
# value is empty. Proof vocabulary.
def kvs.of(ks: List<&2, String>, vs: List<&2, String>) -> List<&2, T.Kv>:
  match ks vs:
    case Nil{} _:
      []
    case Con{_k, _kt} Nil{}:
      []
    case Con{k, kt} Con{v, vt}:
      List.append(&2, T.Kv, L.kv(k, v), kvs.of(kt, vt))

# the same run with every pair written
def full.of(ks: List<&2, String>, vs: List<&2, String>) -> List<&2, T.Kv>:
  match ks vs:
    case Nil{} _:
      []
    case Con{_k, _kt} Nil{}:
      []
    case Con{k, kt} Con{v, vt}:
      T.Kv{k, v} <> full.of(kt, vt)

# whether a key is none of the keys given
def keys.fresh(+key: String, ks: List<&2, String>) -> Bool:
  match ks:
    case []:
      True{}
    case h <> t:
      rest = keys.fresh(key, t)
      Bool.and(Bool.not(String.eq(key, h)), rest)

# whether no key is given twice
def keys.distinct(ks: List<&2, String>) -> Bool:
  match ks:
    case []:
      True{}
    case +h <> +t:
      rest = keys.distinct(t)
      Bool.and(keys.fresh(h, t), rest)

# LAW: a lookup for a key a run does not have finds nothing
law full_absent:
  for +key: String
  for +ks: List<&2, String>
  for +vs: List<&2, String>
  for +e: {keys.fresh(key, ks) == True{} : Bool}
  {T.value(full.of(ks, vs), key) == "" : String}

# by induction on the keys: none is the one looked for
def full_absent(key, ks, vs, e):
  match ks vs:
    case Nil{} _:
      {==}
    case Con{_k, _kt} Nil{}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      f = Equal.sym(Bool, String.eq(k, key), False{},
        Str.eq_flip(key, k, Eq.not.true(String.eq(key, k),
          Eq.and.left(Bool.not(String.eq(key, k)), keys.fresh(key, kt), e))))
      %f : {Bool.pick(String, _, v, T.value(full.of(kt, vt), key)) == "" : String}
      full_absent(key, kt, vt, Eq.and.right(Bool.not(String.eq(key, k)), keys.fresh(key, kt), e))

# LAW: a lookup reads a run with a pair left out when its value is empty as
# the run with every pair written, one pair, with its value and how its key
# compares given
law kvs_full.go:
  for +k: String
  for +kt: List<&2, String>
  for +v: String
  for +vt: List<&2, String>
  for +key: String
  for b: Bool
  for +eb: {String.eq(k, key) == b : Bool}
  for +ef: {keys.fresh(k, kt) == True{} : Bool}
  for ih: {T.value(kvs.of(kt, vt), key) == T.value(full.of(kt, vt), key) : String}
  {T.value(List.append(&2, T.Kv, L.kv(k, v), kvs.of(kt, vt)), key)
    == T.value(T.Kv{k, v} <> full.of(kt, vt), key) : String}

# an empty value is left out, which a lookup for another key does not see
# and a lookup for its own finds nothing where it was
def kvs_full.go(k, kt, v, vt, key, b, eb, ef, ih):
  match v b:
    case SNil{} False{}:
      f = Equal.sym(Bool, String.eq(k, key), False{}, eb)
      %f : {T.value(kvs.of(kt, vt), key) == Bool.pick(String, _, "", T.value(full.of(kt, vt), key))
        : String}
      ih
    case SNil{} True{}:
      f = Equal.sym(Bool, String.eq(k, key), True{}, eb)
      %f : {T.value(kvs.of(kt, vt), key) == Bool.pick(String, _, "", T.value(full.of(kt, vt), key))
        : String}
      Equal.trans(String, T.value(kvs.of(kt, vt), key), T.value(full.of(kt, vt), key), "", ih,
        Equal.trans(String, T.value(full.of(kt, vt), key), T.value(full.of(kt, vt), k), "",
          Equal.cong(String, String, x => T.value(full.of(kt, vt), x), key, k,
            Equal.sym(String, k, key, Str.string_eq_true(k, key, eb))),
          full_absent(k, kt, vt, ef)))
    case SCon{+h, +t} _:
      Equal.cong(String, String, x => Bool.pick(String, String.eq(k, key), SCon{h, t}, x),
        T.value(kvs.of(kt, vt), key), T.value(full.of(kt, vt), key), ih)

# LAW: a lookup reads a run with a pair left out when its value is empty as
# the run with every pair written, when no key is given twice
law kvs_full:
  for +ks: List<&2, String>
  for +vs: List<&2, String>
  for +key: String
  for +e: {keys.distinct(ks) == True{} : Bool}
  {T.value(kvs.of(ks, vs), key) == T.value(full.of(ks, vs), key) : String}

# by induction on the keys
def kvs_full(ks, vs, key, e):
  match ks vs:
    case Nil{} _:
      {==}
    case Con{_k, _kt} Nil{}:
      {==}
    case Con{+k, +kt} Con{+v, +vt}:
      kvs_full.go(k, kt, v, vt, key, String.eq(k, key), {==},
        Eq.and.left(keys.fresh(k, kt), keys.distinct(kt), e),
        kvs_full(kt, vt, key, Eq.and.right(keys.fresh(k, kt), keys.distinct(kt), e)))

# LAW: a workspace member's source reads back from the pairs it is written
# as, with the source taken apart
law src_read.member:
  for +path: String
  for +entry: String
  {L.src_of(L.src.pairs(L.Member{path, entry})) == L.Member{path, entry} : L.Src}

# each value, looked up in the run with every pair written, is the value
def src_read.member(path, entry):
  r0 = Equal.sym(String, T.value(kvs.of(["path", "entry"], [path, entry]), "path"),
    T.value(full.of(["path", "entry"], [path, entry]), "path"),
    kvs_full(["path", "entry"], [path, entry], "path", {==}))
  %r0 : {L.Member{_, T.value(kvs.of(["path", "entry"], [path, entry]), "entry")} == L.Member{path, entry} : L.Src}
  r1 = Equal.sym(String, T.value(kvs.of(["path", "entry"], [path, entry]), "entry"),
    T.value(full.of(["path", "entry"], [path, entry]), "entry"),
    kvs_full(["path", "entry"], [path, entry], "entry", {==}))
  %r1 : {L.Member{T.value(full.of(["path", "entry"], [path, entry]), "path"), _} == L.Member{path, entry} : L.Src}
  {==}

# ---------------------------------------------------------------------------
# a member as a dependency

def Laws.member_dep_walked(
  name,
  ms,
  self,
  files,
  dir,
  nn,
  ee,
  bb,
  hh,
  pa,
  pv,
  ds,
  ts,
  hash,
  root,
  fs,
  sums,
  ef,
  eo,
  en,
  ew
):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds,
      ts}}}, ef)
    : {J.target(_, self, name, files) == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}
  %Equal.sym(Bool, WWorkspace.segs.eq(dir, self), False{}, eo)
    : {J.target.at(_, name, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}, dir, files, self) == J.Got{M.Dep{name,
        hash, J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByHash{}, en)
    : {J.by.name(_, K.of(J.entry.at(dir, ee), files), name, J.entry.at(dir, ee)) == J.Got{M.Dep{name, hash,
        J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}
  %Equal.sym(K.Walked, K.of(J.entry.at(dir, ee), files), K.Walked{hash, root, fs, sums}, ew)
    : {J.walked(_, name, J.entry.at(dir, ee), "") == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root,
        ""}}} : J.Res}
  {==}

def Laws.named_finds(dir, name, ee, bb, hh, pa, pv, ds, ts, ms):
  %Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
    : {J.named.at(_, J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}}, J.named(ms, name))
      == Some{J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}}} : Maybe<&2, J.Member>}
  {==}

def Laws.named_skips(hd, ms, name, en):
  %Equal.sym(Bool, String.eq(J.member.name(hd), name), False{}, en)
    : {J.named.at(_, hd, J.named(ms, name)) == J.named(ms, name) : Maybe<&2, J.Member>}
  {==}

def Laws.member_dep_unknown(name, ms, self, files, ef):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), None{}, ef)
    : {J.target(_, self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and no member's " ++
        "[package] is named " ++ name} : J.Res}
  {==}

def Laws.member_dep_own(name, ms, self, files, dir, mm, ef, eo):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, mm}}, ef)
    : {J.target(_, self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
      : J.Res}
  %Equal.sym(Bool, WWorkspace.segs.eq(dir, self), True{}, eo)
    : {J.target.at(_, name, mm, dir, files, self)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
      : J.Res}
  {==}

def Laws.member_dep_hashed(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(hash), False{}, eg)
    : {J.section(Bool.and(Bool.and(_, String.is_empty(entry)), Bool.and(String.is_empty(path),
        String.is_empty(nv))), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_entried(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(entry), False{}, eg)
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), _), Bool.and(String.is_empty(path),
        String.is_empty(nv))), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(String.is_empty(hash), False{}), False{}, Str.and_false(String.is_empty(hash)))
    : {J.section(Bool.and(_, Bool.and(String.is_empty(path), String.is_empty(nv))), J.named(ms, name), self, name,
        files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_pathed(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(path), False{}, eg)
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), Bool.and(_,
        String.is_empty(nv))), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), False{}), False{},
      Str.and_false(Bool.and(String.is_empty(hash), String.is_empty(entry))))
    : {J.section(_, J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_nv(name, hash, entry, path, nv, ms, self, files, eg):
  %Equal.sym(Bool, String.is_empty(nv), False{}, eg)
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), Bool.and(String.is_empty(path),
        _)), J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(String.is_empty(path), False{}), False{}, Str.and_false(String.is_empty(path)))
    : {J.section(Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), _), J.named(ms, name), self,
        name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  %Equal.sym(Bool, Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)), False{}), False{},
      Str.and_false(Bool.and(String.is_empty(hash), String.is_empty(entry))))
    : {J.section(_, J.named(ms, name), self, name, files)
      == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}
  {==}

def Laws.member_dep_hub(_name, _hash, _entry, _nv, _ms, _self, _files):
  {==}

def Laws.member_dep_git(_name, _hash, _entry, _url, _rev, _tag, _root, _nar, _vend, _ms, _self, _files):
  {==}

def Laws.deps_res_refuses(dd, ds, ms, self, files, why, eb):
  %Equal.sym(J.Res, J.dep.res(dd, ms, self, files), J.Bad{why}, eb)
    : {J.deps.cons(_, J.deps.res(ds, ms, self, files)) == J.Unmet{why} : J.Deps}
  {==}

def Laws.res_one_refuses(dir, mm, ms, files, rest, why, eu):
  %Equal.sym(J.Deps, J.deps.res(J.deps.of(mm), ms, dir, files), J.Unmet{why}, eu)
    : {J.res.put(_, dir, mm, rest) == J.Unread{why} : J.Read}
  {==}

def Laws.res_one_keeps_refusal(dir, mm, ms, files, ds, why, eu):
  %Equal.sym(J.Deps, J.deps.res(J.deps.of(mm), ms, dir, files), J.Deps{ds}, eu)
    : {J.res.put(_, dir, mm, J.Unread{why}) == J.Unread{why} : J.Read}
  {==}

def Laws.resolve_refuses(root, ms, files, why, eu):
  %Equal.sym(J.Read, J.res.all(J.with.root(root, ms), J.with.root(root, ms), files), J.Unread{why}, eu)
    : {J.res.read(_, J.names.deps(J.with.root(root, ms), files)) == J.Clash{why} : J.Joint}
  {==}

def Laws.seed_walked(_nn, hash, entry, path, _nv, files, hw, rw, fs, sums, ew):
  %Equal.sym(K.Walked, K.of(entry, files), K.Walked{hw, rw, fs, sums}, ew)
    : {J.seed.walked(_, hash, path, entry)
      == [W.Reply{W.Pkg{hash, L.Member{path, entry}, ""},
        W.Got{W.Clone{""}, K.manifest_of(sums), J.texts(sums, fs)}}] : List<&2, W.Reply>}
  {==}

def Laws.seed_cloned(_hash, _src, _hub, _nar, _manifest, _ss):
  {==}

def Laws.member_origin(_nn, _hash, _entry, _path, _nv):
  {==}

def Laws.member_judged(_path, _entry, _nar, _hash, _manifest, _ss):
  {==}

def Laws.member_judged_lib(_path, _entry, _hash, _manifest, _ss):
  {==}

def Laws.member_src_reads(path, entry):
  src_read.member(path, entry)

def Laws.member_not_vended(_nn, _hash, _entry, _path, _nv, _ds):
  {==}

def Laws.member_laid(hash, vs, fs, ss, rest, ev):
  %Equal.sym(Bool, String.eq(hash, hash), True{}, Eq.string_eq_self(hash))
    : {P.lay.pick(L.any.step(_, _u => L.seen.holds([], hash)), W.Ok{fs, ss},
        P.place.of(L.seen.holds(vs, hash)), hash, rest)
      == P.lay.verdict(W.Ok{fs, ss}, P.Cache{}, hash, rest) : List<&2, P.Effect>}
  %Equal.sym(Bool, L.seen.holds(vs, hash), False{}, ev)
    : {P.lay.verdict(W.Ok{fs, ss}, P.place.of(_), hash, rest)
      == P.lay.verdict(W.Ok{fs, ss}, P.Cache{}, hash, rest) : List<&2, P.Effect>}
  {==}

def Laws.member_back_kept(_nn, _hash, _entry, _path, _nv, _joint):
  {==}

def Laws.member_not_missing(n, ps, ew):
  %Equal.sym(Bool, M.flag(M.value(ps, "workspace")), True{}, ew)
    : {Bool.and(String.starts_with(n, "deps."), Bool.and(Bool.not(_), String.is_empty(M.value(ps, "hash"))))
      == False{} : Bool}
  Str.and_false(String.starts_with(n, "deps."))
