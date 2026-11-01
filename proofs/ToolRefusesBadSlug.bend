# proofs of laws/ToolRefusesBadSlug.bend
import Base
import ../src/ez/target.bend as Tgt
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP
import ../laws/ToolRefusesBadSlug.bend as Laws
import ./lemmas/PlannerStages.bend as M1

# ---------------------------------------------------------------------------
# laws/ToolRefusesBadSlug.bend

def Laws.remote_refuses_slug(url, slug, bad):
  %Equal.sym(Bool, Tgt.slug.ok(slug), False{}, bad)
    : {Bool.pick(Tgt.Place, _, Tgt.Remote{url, slug}, Tgt.Bad{"not a repository"})
      == Tgt.Bad{"not a repository"} : Tgt.Place}
  {==}

law slug_place:
  for +w: TW.World
  for +url: String
  for +slug: String
  for pl: {TP.place(w) == Tgt.Remote{url, slug} : Tgt.Place}
  for bad: {Tgt.slug.ok(slug) == False{} : Bool}
  {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}

def slug_place(w, url, slug, pl, bad):
  %Equal.sym(Tgt.Place, TP.place(w), Tgt.Remote{url, slug}, pl)
    : {TP.refuses.plan(TP.plan.v(TP.decide.place(_, w), w)) == True{} : Bool}
  %Equal.sym(Bool, Tgt.slug.ok(slug), False{}, bad)
    : {TP.refuses.plan(TP.plan.v(TP.decide.slug(_, url, w), w)) == True{} : Bool}
  {==}

def Laws.tool_refuses_bad_slug(w, url, slug, pl, bad):
  M1.pre(w, slug_place(w, url, slug, pl, bad))

law nowhere_place:
  for +w: TW.World
  for +why: String
  for pl: {TP.place(w) == Tgt.Bad{why} : Tgt.Place}
  {TP.refuses.plan(TP.plan.v(TP.decide.place(TP.place(w), w), w)) == True{} : Bool}

def nowhere_place(w, why, pl):
  %Equal.sym(Tgt.Place, TP.place(w), Tgt.Bad{why}, pl)
    : {TP.refuses.plan(TP.plan.v(TP.decide.place(_, w), w)) == True{} : Bool}
  {==}

def Laws.tool_refuses_nowhere(w, why, pl):
  M1.pre(w, nowhere_place(w, why, pl))
