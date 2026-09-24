# remove: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./plan.bend as RP
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/ignore.bend as I
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ../manifest/LAWS.bend as ML
import ../manifest/PROOF.bend as MP
import ./LAWS.bend as Laws

# LAW: removing committed trees writes nothing at any path
law drops_keep:
  for hs: List<&2, String>
  for +path: String
  {P.put.in(P.drops.of(hs, []), path) == P.Kept{} : P.Wrote}

def drops_keep(hs, path):
  match hs:
    case []:
      {==}
    case _h <> t:
      drops_keep(t, path)

# LAW: nor does the `.gitignore` write, at ez.toml
law ignore_keeps_ledger:
  for b: Bool
  for +next: String
  for hs: List<&2, String>
  {P.put.in(RP.ignore.put(b, next, P.drops.of(hs, [])), "ez.toml") == P.Kept{}
    : P.Wrote}

def ignore_keeps_ledger(b, next, hs):
  match b:
    case True{}:
      drops_keep(hs, "ez.toml")
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(hs, []), "ez.toml"), P.Kept{},
        drops_keep(hs, "ez.toml"))
        : {P.put.one(P.Write{".gitignore", next}, "ez.toml", _) == P.Kept{} : P.Wrote}
      {==}

# LAW: a plan that refuses no ledger it read has no effect when the name is
# absent, and ends in success when it is there
law refused_has:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for r: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == True{} : Bool}
  {P.writes(RP.plan.has(h, m, name, ignore)) == False{} : Bool}

def refused_has(h, m, name, ignore, r):
  match h:
    case True{}:
      Eq.bit.absurd(&2, {P.writes(RP.plan.has(True{}, m, name, ignore)) == False{}
        : Bool}, r)
    case False{}:
      {==}

# LAW: the same for any read of the ledger
law refused_read:
  for led: M.Read
  for +name: String
  for +ignore: String
  for r: {RP.refuses.plan(RP.plan.read(led, name, ignore)) == True{} : Bool}
  {P.writes(RP.plan.read(led, name, ignore)) == False{} : Bool}

def refused_read(led, name, ignore, r):
  match led:
    case M.Bad{_why}:
      {==}
    case M.Good{+m}:
      refused_has(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))), m, name, ignore, r)

def Laws.remove_refusal_writes_nothing(w, r):
  match w:
    case RP.World{+n, l, +ig}:
      refused_read(RP.read.of(l), n, ig, r)

# No ledger reads as the `Bad` arm, which refuses.
def Laws.remove_needs_ledger(_name, _ignore):
  {==}

# The read is rewritten to the `Bad` the premise gives, which refuses.
def Laws.remove_refuses_unread(name, _s, ignore, _why, bad):
  %bad : {RP.refuses.plan(RP.plan.read(_, name, ignore)) == True{} : Bool}
  {==}

# The read is rewritten to the ledger, and the scan for the name to the False
# the premise gives, which is the arm that refuses.
def Laws.remove_refuses_absent(name, _s, ignore, m, good, no):
  %good : {RP.refuses.plan(RP.plan.read(_, name, ignore)) == True{} : Bool}
  %no : {RP.refuses.plan(RP.plan.has(Bool.and(_, Rend.renderable(Rend.remove(m, name))),
    m, name, ignore)) == True{} : Bool}
  {==}

# LAW: a plan over a ledger that names the dependency writes the edited
# ledger to ez.toml; the arm that does not name it refuses, against the
# premise
law edits_has:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for ok: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == False{} : Bool}
  {P.put.plan(RP.plan.has(h, m, name, ignore), "ez.toml")
    == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}

def edits_has(h, m, name, ignore, ok):
  match h:
    case True{}:
      %Equal.sym(P.Wrote,
        P.put.in(RP.ignore.put(
          String.eq(I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore),
          I.sync(RP.deps.of(Rend.remove(m, name)), ignore),
          P.drops.of(RP.gone(RP.deps.of(m), name, RP.deps.of(Rend.remove(m, name))), [])),
          "ez.toml"),
        P.Kept{},
        ignore_keeps_ledger(
          String.eq(I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore),
          I.sync(RP.deps.of(Rend.remove(m, name)), ignore),
          RP.gone(RP.deps.of(m), name, RP.deps.of(Rend.remove(m, name)))))
        : {P.put.one(P.Write{"ez.toml", Rend.show(Rend.remove(m, name))}, "ez.toml", _)
          == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}
      {==}
    case False{}:
      Eq.bit.absurd2(&2, {P.put.plan(RP.plan.has(False{}, m, name, ignore), "ez.toml")
        == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}, ok)

# The read is rewritten to the ledger in the goal, and in the premise by the
# same equation carried through `refuses.plan`.
def Laws.remove_edits_ledger(name, s, ignore, m, good, ok):
  %good : {P.put.plan(RP.plan.read(_, name, ignore), "ez.toml")
    == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}
  edits_has(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))), m, name, ignore,
    Equal.trans(Bool,
      RP.refuses.plan(RP.plan.read(M.Good{m}, name, ignore)),
      RP.refuses.plan(RP.plan.read(M.parse(s), name, ignore)),
      False{},
      Equal.cong(M.Read, Bool, x => RP.refuses.plan(RP.plan.read(x, name, ignore)),
        M.Good{m}, M.parse(s), good),
      ok))

# LAW: what `.gitignore` holds after the edits: the text `I.sync` gave,
# whether it was written or, being the same text, kept
law syncs_arm:
  for b: Bool
  for +next: String
  for +ignore: String
  for +text: String
  for hs: List<&2, String>
  for eb: {String.eq(next, ignore) == b : Bool}
  {RP.after(P.put.in(P.Write{"ez.toml", text} <> RP.ignore.put(b, next,
    P.drops.of(hs, [])), ".gitignore"), ignore) == next : String}

def syncs_arm(b, next, ignore, text, hs, eb):
  match b:
    case True{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(hs, []), ".gitignore"), P.Kept{},
        drops_keep(hs, ".gitignore"))
        : {RP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore", _), ignore)
          == next : String}
      Equal.sym(String, next, ignore, Str.string_eq_true(next, ignore, eb))
    case False{}:
      %Equal.sym(P.Wrote, P.put.in(P.drops.of(hs, []), ".gitignore"), P.Kept{},
        drops_keep(hs, ".gitignore"))
        : {RP.after(P.put.one(P.Write{"ez.toml", text}, ".gitignore",
          P.put.one(P.Write{".gitignore", next}, ".gitignore", _)), ignore)
          == next : String}
      {==}

# LAW: over a ledger that names the dependency; the other arm refuses
law syncs_has:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for ok: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == False{} : Bool}
  {RP.after(P.put.plan(RP.plan.has(h, m, name, ignore), ".gitignore"), ignore)
    == I.sync(RP.deps.of(Rend.remove(m, name)), ignore) : String}

def syncs_has(h, m, name, ignore, ok):
  match h:
    case True{}:
      syncs_arm(String.eq(I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore),
        I.sync(RP.deps.of(Rend.remove(m, name)), ignore), ignore,
        Rend.show(Rend.remove(m, name)),
        RP.gone(RP.deps.of(m), name, RP.deps.of(Rend.remove(m, name))), {==})
    case False{}:
      Eq.bit.absurd2(&2, {RP.after(P.put.plan(RP.plan.has(False{}, m, name, ignore),
        ".gitignore"), ignore) == I.sync(RP.deps.of(Rend.remove(m, name)), ignore)
        : String}, ok)

def Laws.remove_syncs_allowlist(name, s, ignore, m, good, ok):
  %good : {RP.after(P.put.plan(RP.plan.read(_, name, ignore), ".gitignore"), ignore)
    == I.sync(RP.deps.of(Rend.remove(m, name)), ignore) : String}
  syncs_has(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))), m, name, ignore,
    Equal.trans(Bool,
      RP.refuses.plan(RP.plan.read(M.Good{m}, name, ignore)),
      RP.refuses.plan(RP.plan.read(M.parse(s), name, ignore)),
      False{},
      Equal.cong(M.Read, Bool, x => RP.refuses.plan(RP.plan.read(x, name, ignore)),
        M.Good{m}, M.parse(s), good),
      ok))

# EZ-LED-5: `Rend.remove` edits the dependencies and hands the tools on as
# they are, and a name that only a tool has is a name the dependencies lack,
# which `remove_refuses_absent` refuses whatever the tools are.
def Laws.remove_keeps_tools(name, s, ignore, n, e, b, h, hpa, hpv, ds, ts, good, ok):
  Laws.remove_edits_ledger(name, s, ignore, M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, good, ok)

def Laws.remove_refuses_tool(name, s, ignore, n, e, b, h, hpa, hpv, ds, ts, good, _tool, no):
  Laws.remove_refuses_absent(name, s, ignore, M.Manifest{n, e, b, h, hpa, hpv, ds, ts}, good, no)

# ---------------------------------------------------------------------------
# EZ-OUT-1

# LAW: a plan ends with the status of whether it refuses
law plan_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(RP.refuses.plan(pl)) : U32}

def plan_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.remove_exits_as_it_refuses(w):
  plan_code(RP.plan(w))

# ---------------------------------------------------------------------------
# EZ-LED-4

# what a path was written with. Proof vocabulary.
def wrote.text(w: P.Wrote) -> String:
  match w:
    case P.Kept{}:
      ""
    case P.Put{t}:
      t

# LAW: a plan over a ledger that does not refuse was given True
law has_ok:
  for h: Bool
  for +m: M.Manifest
  for +name: String
  for +ignore: String
  for ok: {RP.refuses.plan(RP.plan.has(h, m, name, ignore)) == False{} : Bool}
  {h == True{} : Bool}

def has_ok(h, _m, _name, _ignore, ok):
  match h:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, ok)

# A remove that does not refuse writes `Rend.remove`'s ledger, which it made
# sure is renderable, so the manifest's round trip reads it back.
def Laws.remove_ledger_reads_back(name, s, ignore, m, text, good, ok, put):
  +ok2 = Equal.trans(Bool,
    RP.refuses.plan(RP.plan.read(M.Good{m}, name, ignore)),
    RP.refuses.plan(RP.plan.read(M.parse(s), name, ignore)),
    False{},
    Equal.cong(M.Read, Bool, x => RP.refuses.plan(RP.plan.read(x, name, ignore)),
      M.Good{m}, M.parse(s), good),
    ok)
  +er = Eq.and.right(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name)),
    has_ok(Bool.and(RP.named(RP.deps.of(m), name), Rend.renderable(Rend.remove(m, name))),
      m, name, ignore, ok2))
  +p = Equal.trans(P.Wrote, P.Put{Rend.show(Rend.remove(m, name))},
    P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml"), P.Put{text},
    Equal.sym(P.Wrote, P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml"),
      P.Put{Rend.show(Rend.remove(m, name))}, Laws.remove_edits_ledger(name, s, ignore, m, good, ok)),
    put)
  +t = Equal.cong(P.Wrote, String, w => wrote.text(w), P.Put{Rend.show(Rend.remove(m, name))},
    P.Put{text}, p)
  %t : {M.parse(_) == M.Good{Rend.remove(m, name)} : M.Read}
  ML.ledger_reads_back(Rend.remove(m, name), er)
