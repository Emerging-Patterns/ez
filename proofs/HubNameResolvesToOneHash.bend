# proofs of laws/HubNameResolvesToOneHash.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/hub.bend as H
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/HubNameResolvesToOneHash.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

# LAW: one name of a list the table resolves, with whether it is the one
# looked for decided
law nm.queued.step:
  for +c: Bool
  for +ns: List<&2, L.Name>
  for +h: String
  for +t: List<&2, String>
  for +nv: String
  for +ec: {c == String.eq(h, nv) : Bool}
  for +e: {L.any.step(c, _u => L.seen.holds(t, nv)) == True{} : Bool}
  for +f: {False{} == String.is_empty(L.name.find(ns, nv)) : Bool}
  for ih: {L.seen.holds(t, nv) == True{} : Bool}
    -> {L.seen.holds(L.name.hashes(ns, t), L.name.find(ns, nv)) == True{} : Bool}
  {L.seen.holds(List.append(&2, String, L.name.put(L.name.find(ns, h)), L.name.hashes(ns, t)),
    L.name.find(ns, nv)) == True{} : Bool}

def nm.queued.step(c, ns, h, t, nv, ec, e, f, ih):
  match c:
    case True{}:
      +hn = Str.string_eq_true(h, nv, Equal.sym(Bool, True{}, String.eq(h, nv), ec))
      %Equal.sym(String, h, nv, hn)
        : {L.seen.holds(List.append(&2, String, L.name.put(L.name.find(ns, _)), L.name.hashes(ns, t)),
          L.name.find(ns, nv)) == True{} : Bool}
      %f : {L.seen.holds(List.append(&2, String,
          Bool.pick(List<&2, String>, _, [], [L.name.find(ns, nv)]), L.name.hashes(ns, t)),
          L.name.find(ns, nv)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(L.name.find(ns, nv), L.name.find(ns, nv)), True{},
        Eq.string_eq_self(L.name.find(ns, nv)))
        : {L.any.step(_, _u => L.seen.holds(L.name.hashes(ns, t), L.name.find(ns, nv))) == True{}
          : Bool}
      {==}
    case False{}:
      M2.holds_right(L.name.put(L.name.find(ns, h)), L.name.hashes(ns, t), L.name.find(ns, nv), ih(e))

def Laws.named_kid_queued(ns, nvs, nv, e, f):
  match nvs:
    case []:
      Eq.bit.absurd(&2, {L.seen.holds(L.name.hashes(ns, []), L.name.find(ns, nv)) == True{} : Bool}, e)
    case +h <> +t:
      nm.queued.step(String.eq(h, nv), ns, h, t, nv, {==}, e, f,
        z => Laws.named_kid_queued(ns, t, nv, z, f))

# LAW: a name the table gives the hash of, as the lock records it, agrees
# with the table, or is not recorded
law nm.agree_pick:
  for +b: Bool
  for +ns: List<&2, L.Name>
  for +h: String
  {Laws.names.agree(ns, Bool.pick(List<&2, L.Name>, b, [], [L.Name{h, L.name.find(ns, h)}]))
    == True{} : Bool}

def nm.agree_pick(b, ns, h):
  match b:
    case True{}:
      {==}
    case False{}:
      M1.and_true(String.eq(L.name.find(ns, h), L.name.find(ns, h)), True{},
        Eq.string_eq_self(L.name.find(ns, h)), {==})

# LAW: two lists that agree with a table, joined, agree with it
law nm.agree_app:
  for +ns: List<&2, L.Name>
  for +xs: List<&2, L.Name>
  for +ys: List<&2, L.Name>
  for +ex: {Laws.names.agree(ns, xs) == True{} : Bool}
  for +ey: {Laws.names.agree(ns, ys) == True{} : Bool}
  {Laws.names.agree(ns, List.append(&2, L.Name, xs, ys)) == True{} : Bool}

def nm.agree_app(ns, xs, ys, ex, ey):
  match xs:
    case []:
      ey
    case L.Name{+n, +h} <> +t:
      M1.and_true(String.eq(L.name.find(ns, n), h),
        Laws.names.agree(ns, List.append(&2, L.Name, t, ys)),
        Eq.and.left(String.eq(L.name.find(ns, n), h), Laws.names.agree(ns, t), ex),
        nm.agree_app(ns, t, ys,
          Eq.and.right(String.eq(L.name.find(ns, n), h), Laws.names.agree(ns, t), ex), ey))

def Laws.lock_names_agree(ns, nvs):
  match nvs:
    case []:
      {==}
    case +h <> +t:
      nm.agree_app(ns, L.name.one(h, L.name.find(ns, h)), L.name.pairs(ns, t),
        nm.agree_pick(String.is_empty(L.name.find(ns, h)), ns, h),
        Laws.lock_names_agree(ns, t))

# ---------------------------------------------------------------------------
# the hash recorded is the one the hub answered
# (laws/HubNameResolvesToOneHash.bend)

# whether a verdict that has a package has it under this hash. Proof
# vocabulary.
def hnb(v: H.Verdict, +t: String) -> Bool:
  match v:
    case H.Go{h, _fs, _ss}:
      String.eq(h, t)
    case H.Pending{_asks}:
      True{}
    case H.Stop{_why}:
      True{}

law hnb_body:
  for vv: W.Verdict
  for +hash: String
  {hnb(H.decide.body(vv, hash), hash) == True{} : Bool}

def hnb_body(vv, hash):
  match vv:
    case W.Ok{_fs, _ss}:
      Eq.string_eq_self(hash)
    case W.No{_why}:
      {==}
    case W.Named{_ns}:
      {==}

law hnb_got:
  for a: W.Answer
  for +hash: String
  for +w: A.World
  {hnb(H.decide.got(a, hash, w), hash) == True{} : Bool}

def hnb_got(a, hash, _w):
  match a:
    case W.Got{how, manifest, ss}:
      hnb_body(W.hub.how(how, hash, manifest, ss), hash)
    case W.Miss{_why}:
      {==}
    case W.Said{_text}:
      {==}
    case W.Locked{_text}:
      {==}

law hnb_pkg:
  for g: Maybe<&2, W.Answer>
  for +hash: String
  for +w: A.World
  {hnb(H.decide.pkg(g, hash, w), hash) == True{} : Bool}

def hnb_pkg(g, hash, w):
  match g:
    case None{}:
      {==}
    case Some{a}:
      hnb_got(a, hash, w)

law hnb_hash:
  for ok: Bool
  for +hash: String
  for +w: A.World
  {hnb(H.decide.hash(ok, hash, w), hash) == True{} : Bool}

def hnb_hash(ok, hash, w):
  match ok:
    case True{}:
      hnb_pkg(H.heard(A.hubs(w), hash), hash, w)
    case False{}:
      {==}

law hnb_early:
  for b: Bool
  for +why: String
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  {hnb(H.decide.early(b, why, w), String.trim(text)) == True{} : Bool}

def hnb_early(b, _why, w, text, said):
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, W.Answer>, H.heard(A.hubs(w), A.target(w)), Some{W.Said{text}}, said)
        : {hnb(H.decide.name(_, w), String.trim(text)) == True{} : Bool}
      hnb_hash(L.hash.ok(String.trim(text)), String.trim(text), w)
    case False{}:
      {==}

law hnb_read:
  for r: M.Read
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  {hnb(H.decide.read(r, w), String.trim(text)) == True{} : Bool}

def hnb_read(r, w, text, said):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      hnb_early(String.is_empty(H.early(w)), H.early(w), w, text, said)

# LAW: a verdict that does not refuse has its package under the hash it is
# known to name
law hnb_hash_is:
  for v: H.Verdict
  for +t: String
  for +w: A.World
  for e: {hnb(v, t) == True{} : Bool}
  for ok: {H.refuses.plan(H.plan.v(v, w)) == False{} : Bool}
  {H.verdict.hash(v) == t : String}

def hnb_hash_is(v, t, _w, e, ok):
  match v:
    case H.Go{h, _fs, _ss}:
      Str.string_eq_true(h, t, e)
    case H.Pending{asks}:
      Eq.bit.absurd2(&2, {H.verdict.hash(H.Pending{asks}) == t : String}, ok)
    case H.Stop{why}:
      Eq.bit.absurd2(&2, {H.verdict.hash(H.Stop{why}) == t : String}, ok)

def Laws.add_named_records_name(w, text, said, ok):
  Equal.cong(String, M.Dep, x => M.Dep{H.key(w), x, M.dep.entry(H.added(w)),
      M.Hub{A.target(w)}}, H.hash(w), String.trim(text),
    hnb_hash_is(H.decide(w), String.trim(text), w, hnb_read(A.read(w), w, text, said), ok))

# ---------------------------------------------------------------------------
# every question names the ledger's hub (laws/HubNameResolvesToOneHash.bend)

law hah_body:
  for vv: W.Verdict
  for +hash: String
  for +hub: String
  {H.asks.hub(H.asks.v(H.decide.body(vv, hash)), hub) == True{} : Bool}

def hah_body(vv, _hash, _hub):
  match vv:
    case W.Ok{_fs, _ss}:
      {==}
    case W.No{_why}:
      {==}
    case W.Named{_ns}:
      {==}

law hah_got:
  for a: W.Answer
  for +hash: String
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.got(a, hash, w)), A.hub(w)) == True{} : Bool}

def hah_got(a, hash, w):
  match a:
    case W.Got{how, manifest, ss}:
      hah_body(W.hub.how(how, hash, manifest, ss), hash, A.hub(w))
    case W.Miss{_why}:
      {==}
    case W.Said{_text}:
      {==}
    case W.Locked{_text}:
      {==}

law hah_pkg:
  for g: Maybe<&2, W.Answer>
  for +hash: String
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.pkg(g, hash, w)), A.hub(w)) == True{} : Bool}

def hah_pkg(g, hash, w):
  match g:
    case None{}:
      %Equal.sym(Bool, String.eq(A.hub(w), A.hub(w)), True{}, Eq.string_eq_self(A.hub(w)))
        : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Some{a}:
      hah_got(a, hash, w)

law hah_hash:
  for ok: Bool
  for +hash: String
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.hash(ok, hash, w)), A.hub(w)) == True{} : Bool}

def hah_hash(ok, hash, w):
  match ok:
    case True{}:
      hah_pkg(H.heard(A.hubs(w), hash), hash, w)
    case False{}:
      {==}

law hah_said:
  for a: W.Answer
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.said(a, w)), A.hub(w)) == True{} : Bool}

def hah_said(a, w):
  match a:
    case W.Said{+text}:
      hah_hash(L.hash.ok(String.trim(text)), String.trim(text), w)
    case W.Got{_how, _manifest, _ss}:
      {==}
    case W.Miss{_why}:
      {==}
    case W.Locked{_text}:
      {==}

law hah_name:
  for g: Maybe<&2, W.Answer>
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.name(g, w)), A.hub(w)) == True{} : Bool}

def hah_name(g, w):
  match g:
    case None{}:
      %Equal.sym(Bool, String.eq(A.hub(w), A.hub(w)), True{}, Eq.string_eq_self(A.hub(w)))
        : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Some{a}:
      hah_said(a, w)

law hah_early:
  for b: Bool
  for +why: String
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.early(b, why, w)), A.hub(w)) == True{} : Bool}

def hah_early(b, _why, w):
  match b:
    case True{}:
      hah_name(H.heard(A.hubs(w), A.target(w)), w)
    case False{}:
      {==}

law hah_read:
  for r: M.Read
  for +w: A.World
  {H.asks.hub(H.asks.v(H.decide.read(r, w)), A.hub(w)) == True{} : Bool}

def hah_read(r, w):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      hah_early(String.is_empty(H.early(w)), H.early(w), w)

def Laws.add_named_asks_hub(w):
  hah_read(A.read(w), w)

# ---------------------------------------------------------------------------
# names (EZ-HUB)

law nm.agree_held:
  for same: Bool
  for +nv: String
  for +hash: String
  for +was: String
  {Laws.put.agrees(nv, hash, FP.name.held(same, nv, hash, was)) == True{} : Bool}

def nm.agree_held(same, nv, hash, _was):
  match same:
    case True{}:
      {==}
    case False{}:
      Str.and_true(String.eq(nv, nv), String.eq(hash, hash), Eq.string_eq_self(nv),
        Eq.string_eq_self(hash))

law nm.agree_got:
  for got: Maybe<&2, String>
  for +nv: String
  for +hash: String
  {Laws.put.agrees(nv, hash, FP.name.got(got, nv, hash)) == True{} : Bool}

def nm.agree_got(got, nv, hash):
  match got:
    case None{}:
      Str.and_true(String.eq(nv, nv), String.eq(hash, hash), Eq.string_eq_self(nv),
        Eq.string_eq_self(hash))
    case Some{+text}:
      nm.agree_held(String.eq(String.trim(text), hash), nv, hash, String.trim(text))

law nm.agree_answer:
  for a: F.Answer
  for +nv: String
  for +hash: String
  {Laws.put.agrees(nv, hash, FP.name.answer(a, nv, hash)) == True{} : Bool}

def nm.agree_answer(a, nv, hash):
  match a:
    case F.Held{got}:
      nm.agree_got(got, nv, hash)
    case F.Read{_x}:
      {==}
    case F.Said{_x}:
      {==}
    case F.Seen{_x}:
      {==}

law nm.agree_heard:
  for g: F.Heard
  for +nv: String
  for +hash: String
  {Laws.put.agrees(nv, hash, FP.name.heard(g, nv, hash)) == True{} : Bool}

def nm.agree_heard(g, nv, hash):
  match g:
    case F.Open{}:
      {==}
    case F.Heard{a}:
      nm.agree_answer(a, nv, hash)

law nm.agree_valid:
  for b: Bool
  for +rs: List<&2, F.Reply>
  for +nv: String
  for +hash: String
  {Laws.put.agrees(nv, hash, FP.name.valid(b, rs, nv, hash)) == True{} : Bool}

def nm.agree_valid(b, rs, nv, hash):
  match b:
    case True{}:
      nm.agree_heard(F.heard(rs, F.Named{nv}), nv, hash)
    case False{}:
      {==}

def Laws.fetch_names_the_lock(rs, nv, hash):
  nm.agree_valid(L.name.valid(L.Name{nv, hash}), rs, nv, hash)
