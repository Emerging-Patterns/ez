# proofs of laws/LockReproducible.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../laws/HashPathIsHubImport.bend as L1
import ../laws/LockReproducible.bend as Laws
import ../laws/ImportHashIsFirstComponent.bend as L2
import ../laws/defs/Slashless.bend as D1
import ./lemmas/ContainsSlash.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

# LAW: how the bytes arrived, as a fresh clone would have it, is judged as it
# was, for a source of either kind
law reclone.how_judged:
  for src: L.Src
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(src, W.reclone.how(how, src), hash, manifest, ss)
    == W.accept.src(src, how, hash, manifest, ss) : W.Verdict}

def reclone.how_judged(src, how, hash, manifest, ss):
  match how:
    case W.Lib{}:
      Equal.sym(W.Verdict,
        W.accept.src(src, W.Lib{}, hash, manifest, ss),
        W.accept.src(src, W.Clone{L.src.nar(src)}, hash, manifest, ss),
        M2.lib_as_clone.src(src, hash, manifest, ss))
    case W.Clone{got}:
      {==}
    case W.Served{}:
      {==}

# LAW: one answer, as a fresh clone would have it, is judged as it was
law reclone.one_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {W.accept(orgs, hub, hash, W.reclone.one(orgs, hash, a))
    == W.accept(orgs, hub, hash, a) : W.Verdict}

def reclone.one_judged(orgs, _hub, hash, a):
  match a:
    case W.Miss{why}:
      {==}
    case W.Got{how, manifest, ss}:
      reclone.how_judged(L.origin(orgs, hash), how, hash, manifest, ss)
    case W.Said{_text}:
      {==}
    case W.Locked{_text}:
      {==}

# LAW: every answer, as a fresh clone would have it, is judged as it was
law reclone_judged:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {W.judge(orgs, hub, W.reclone.all(orgs, rs)) == W.judge(orgs, hub, rs)
    : List<&2, W.Judged>}

def reclone_judged(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{+ask, a} <> t:
      Equal.trans(List<&2, W.Judged>,
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask),
          W.reclone.one(orgs, W.ask.hash(ask), a))}
          <> W.judge(orgs, hub, W.reclone.all(orgs, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, W.reclone.all(orgs, t)),
        W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)}
          <> W.judge(orgs, hub, t),
        Equal.cong(W.Verdict, List<&2, W.Judged>,
          v => W.Judged{W.ask.hash(ask), v} <> W.judge(orgs, hub, W.reclone.all(orgs, t)),
          W.accept(orgs, hub, W.ask.hash(ask), W.reclone.one(orgs, W.ask.hash(ask), a)),
          W.accept(orgs, hub, W.ask.hash(ask), a),
          reclone.one_judged(orgs, hub, W.ask.hash(ask), a)),
        Equal.cong(List<&2, W.Judged>, List<&2, W.Judged>,
          js => W.Judged{W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)} <> js,
          W.judge(orgs, hub, W.reclone.all(orgs, t)),
          W.judge(orgs, hub, t),
          reclone_judged(orgs, hub, t)))

# LAW: a fresh clone's World has the Inputs of the World it was made from
law reclone_inputs:
  for w: W.World
  {W.inputs(W.reclone(w)) == W.inputs(w) : W.Inputs}

def reclone_inputs(w):
  match w:
    case W.World{+args, +ledger, listing, replies, +ups}:
      Equal.cong(List<&2, W.Judged>, W.Inputs,
        js => W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          List.append(&2, W.Judged,
            W.judge(W.next.origins(W.next(args, ledger, ups)),
              W.next.hub(W.next(args, ledger, ups)),
              W.laid.replies(Up.next.trees(W.next(args, ledger, ups)),
                W.next.origins(W.next(args, ledger, ups)),
                W.next.hub(W.next(args, ledger, ups)))), js)},
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)),
          W.reclone.all(W.next.origins(W.next(args, ledger, ups)), replies)),
        W.judge(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies),
        reclone_judged(W.next.origins(W.next(args, ledger, ups)),
          W.next.hub(W.next(args, ledger, ups)), replies))

def Laws.clone_reproduces(w):
  Laws.lock_reproducible(W.reclone(w), w, reclone_inputs(w))

# LAW: a character of a solid string is not blank
law solid.head:
  for +h: Char
  for t: String
  for e: {Laws.solid(SCon{h, t}) == True{} : Bool}
  {K.blank(h) == False{} : Bool}

def solid.head(h, t, e):
  Eq.not.true(K.blank(h), Eq.and.left(Bool.not(K.blank(h)), Laws.solid(t), e))

# LAW: and the rest of it is solid
law solid.tail:
  for +h: Char
  for t: String
  for e: {Laws.solid(SCon{h, t}) == True{} : Bool}
  {Laws.solid(t) == True{} : Bool}

def solid.tail(h, t, e):
  Eq.and.right(Bool.not(K.blank(h)), Laws.solid(t), e)

# LAW: two solid strings make a solid one
law solid.app:
  for a: String
  for b: String
  for +ea: {Laws.solid(a) == True{} : Bool}
  for eb: {Laws.solid(b) == True{} : Bool}
  {Laws.solid(a ++ b) == True{} : Bool}

def solid.app(a, b, ea, eb):
  match a:
    case SNil{}:
      eb
    case SCon{+h, +t}:
      %Equal.sym(Bool, K.blank(h), False{}, solid.head(h, t, ea))
        : {Bool.and(Bool.not(_), Laws.solid(t ++ b)) == True{} : Bool}
      solid.app(t, b, solid.tail(h, t, ea), eb)

# LAW: the path of a hub import is solid
law spec.solid:
  for hash: String
  for path: String
  for hs: {Laws.solid(hash) == True{} : Bool}
  for pp: {Laws.solid(path) == True{} : Bool}
  {Laws.solid("0x" ++ (hash ++ SCon{'/', path})) == True{} : Bool}

def spec.solid(hash, path, hs, pp):
  solid.app(hash, SCon{'/', path}, hs, pp)

# the trim

# LAW: a run of spaces and tabs in front of a line is gone from its trim
law gap_front:
  for gs: List<&2, Laws.Gap>
  for s: String
  {K.trim.front(Laws.gap(gs) ++ s) == K.trim.front(s) : String}

def gap_front(gs, s):
  match gs:
    case []:
      {==}
    case g <> t:
      match g:
        case Laws.Sp{}:
          gap_front(t, s)
        case Laws.Tab{}:
          gap_front(t, s)

# LAW: a run of spaces and tabs alone trims to nothing from the back
law gap_back:
  for gs: List<&2, Laws.Gap>
  {K.trim.back(Laws.gap(gs)) == "" : String}

def gap_back(gs):
  match gs:
    case []:
      {==}
    case g <> t:
      match g:
        case Laws.Sp{}:
          %Equal.sym(String, K.trim.back(Laws.gap(t)), "", gap_back(t))
            : {K.trim.back.at(Bool.and(True{}, String.is_empty(_)), ' ', _) == ""
            : String}
          {==}
        case Laws.Tab{}:
          %Equal.sym(String, K.trim.back(Laws.gap(t)), "", gap_back(t))
            : {K.trim.back.at(Bool.and(True{}, String.is_empty(_)), '\t', _) == ""
            : String}
          {==}

# LAW: a solid string before blanks the back trims away is what is left
law solid_back:
  for s: String
  for +g: String
  for +e: {Laws.solid(s) == True{} : Bool}
  for eg: {K.trim.back(g) == "" : String}
  {K.trim.back(s ++ g) == s : String}

def solid_back(s, g, e, eg):
  match s:
    case SNil{}:
      eg
    case SCon{+h, +t}:
      %Equal.sym(Bool, K.blank(h), False{}, solid.head(h, t, e)) : {K.trim.back.at(Bool.and(_,
        String.is_empty(K.trim.back(t ++ g))), h, K.trim.back(t ++ g)) == SCon{h, t} : String}
      %Equal.sym(String, K.trim.back(t ++ g), t, solid_back(t, g, solid.tail(h, t, e), eg))
        : {K.trim.back.at(False{}, h, _)
        == SCon{h, t} : String}
      {==}

# LAW: a string with something after it is not empty
law app_full:
  for t: String
  for d: Char
  for u: String
  {String.is_empty(t ++ SCon{d, u}) == False{} : Bool}

def app_full(t, _d, _u):
  match t:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

# LAW: a character before a line whose back trim is not empty is kept
law keep_at:
  for b: Bool
  for h: Char
  for r: String
  {K.trim.back.at(Bool.and(b, False{}), h, r) == SCon{h, r} : String}

def keep_at(b, _h, _r):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: what stands before a line whose back trim is not empty is kept whole
law back_keep:
  for a: String
  for +y: String
  for +d: Char
  for +u: String
  for e: {K.trim.back(y) == SCon{d, u} : String}
  {K.trim.back(a ++ y) == a ++ SCon{d, u} : String}

def back_keep(a, y, d, u, e):
  match a:
    case SNil{}:
      e
    case SCon{+h, +t}:
      %Equal.sym(String, K.trim.back(t ++ y), t ++ SCon{d, u}, back_keep(t, y, d, u, e))
        : {K.trim.back.at(Bool.and(K.blank(h), String.is_empty(_)), h,
        _) == SCon{h, t ++ SCon{d, u}} : String}
      %Equal.sym(Bool, String.is_empty(t ++ SCon{d, u}), False{}, app_full(t, d, u))
        : {K.trim.back.at(Bool.and(K.blank(h), _), h, t ++ SCon{d, u})
        == SCon{h, t ++ SCon{d, u}} : String}
      keep_at(K.blank(h), h, t ++ SCon{d, u})

# the line from `import` to the end of its name
def line.core(
  o: Laws.Gap,
  os: List<&2, Laws.Gap>,
  hash: String,
  path: String,
  w: Laws.Gap,
  ws: List<&2, Laws.Gap>,
  r: Laws.Gap,
  rs: List<&2, Laws.Gap>,
  n: Char,
  ns: String
) -> String:
  "import" ++ (Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
    ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})))))

# LAW: the trim of a hub import line is the line from `import` to the end of
# its name
law line_trim:
  for +lead: List<&2, Laws.Gap>
  for +o: Laws.Gap
  for +os: List<&2, Laws.Gap>
  for +hash: String
  for +path: String
  for +w: Laws.Gap
  for +ws: List<&2, Laws.Gap>
  for +r: Laws.Gap
  for +rs: List<&2, Laws.Gap>
  for +n: Char
  for +ns: String
  for +tail: List<&2, Laws.Gap>
  for np: {Laws.solid(SCon{n, ns}) == True{} : Bool}
  {K.trim(Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail))
    == line.core(o, os, hash, path, w, ws, r, rs, n, ns) : String}

def line_trim(lead, o, os, hash, path, w, ws, r, rs, n, ns, tail, np):
  %Equal.sym(String,
    K.trim.front(Laws.gap(lead) ++ ("import" ++ (Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail))))))))),
    K.trim.front("import" ++ (Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail)))))))),
    gap_front(lead, "import" ++ (Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail)))))))))
    : {K.trim.back(_) == line.core(o, os, hash, path, w, ws, r, rs, n, ns) : String}
  back_keep("import", Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail)))))),
    Laws.gap.char(o), Laws.gap(os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})))),
  back_keep(Laws.gap(o <> os), ("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail))))),
    '0', "x" ++ ((hash ++ SCon{'/', path})
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})))),
  back_keep("0x" ++ (hash ++ SCon{'/', path}),
      Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail)))),
    Laws.gap.char(w), Laws.gap(ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})),
  back_keep(Laws.gap(w <> ws), "as" ++ (Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail))),
    'a', "s" ++ (Laws.gap(r <> rs) ++ SCon{n, ns}),
  back_keep("as", Laws.gap(r <> rs) ++ (SCon{n, ns} ++ Laws.gap(tail)),
    Laws.gap.char(r), Laws.gap(rs) ++ SCon{n, ns},
  back_keep(Laws.gap(r <> rs), SCon{n, ns} ++ Laws.gap(tail), n, ns,
    solid_back(SCon{n, ns}, Laws.gap(tail), np, gap_back(tail))))))))

# the fields

# LAW: a solid string before a gap is one field, ahead of the fields after the
# gap
law cut_solid:
  for s: String
  for x: String
  for a: List<&2, String>
  for +e: {Laws.solid(s) == True{} : Bool}
  for ec: {K.cut(x) == K.Cut{"", a} : K.Cut}
  {K.cut(s ++ x) == K.Cut{s, a} : K.Cut}

def cut_solid(s, x, a, e, ec):
  match s:
    case SNil{}:
      ec
    case SCon{+h, +t}:
      %Equal.sym(Bool, K.blank(h), False{}, solid.head(h, t, e))
        : {K.cut.at(_, h, K.cut(t ++ x)) == K.Cut{SCon{h, t}, a} : K.Cut}
      %Equal.sym(K.Cut, K.cut(t ++ x), K.Cut{t, a}, cut_solid(t, x, a, solid.tail(h, t, e), ec))
        : {K.cut.at(False{}, h, _) == K.Cut{SCon{h, t}, a} : K.Cut}
      {==}

# LAW: a run of spaces and tabs ends the field under way and starts none
law cut_gap:
  for run: List<&2, Laws.Gap>
  for first: Laws.Gap
  for x: String
  for +f: String
  for +a: List<&2, String>
  for ec: {K.cut(x) == K.Cut{f, a} : K.Cut}
  {K.cut(Laws.gap(first <> run) ++ x) == K.Cut{"", K.cut.put(f, a)} : K.Cut}

def cut_gap(run, first, x, f, a, ec):
  match run first:
    case Nil{} Laws.Sp{}:
      %Equal.sym(K.Cut, K.cut(x), K.Cut{f, a}, ec)
        : {K.cut.at(True{}, ' ', _) == K.Cut{"", K.cut.put(f, a)} : K.Cut}
      {==}
    case Nil{} Laws.Tab{}:
      %Equal.sym(K.Cut, K.cut(x), K.Cut{f, a}, ec)
        : {K.cut.at(True{}, '\t', _) == K.Cut{"", K.cut.put(f, a)} : K.Cut}
      {==}
    case Con{+g2, +t} Laws.Sp{}:
      %Equal.sym(K.Cut, K.cut(Laws.gap(g2 <> t) ++ x), K.Cut{"", K.cut.put(f, a)},
        cut_gap(t, g2, x, f, a, ec))
        : {K.cut.at(True{}, ' ', _) == K.Cut{"", K.cut.put(f, a)} : K.Cut}
      {==}
    case Con{+g2, +t} Laws.Tab{}:
      %Equal.sym(K.Cut, K.cut(Laws.gap(g2 <> t) ++ x), K.Cut{"", K.cut.put(f, a)},
        cut_gap(t, g2, x, f, a, ec))
        : {K.cut.at(True{}, '\t', _) == K.Cut{"", K.cut.put(f, a)} : K.Cut}
      {==}

# LAW: a solid string alone is one field
law cut_one:
  for +s: String
  for e: {Laws.solid(s) == True{} : Bool}
  {K.cut(s) == K.Cut{s, []} : K.Cut}

def cut_one(s, e):
  %Eq.append_nil(s) : {K.cut(_) == K.Cut{s, []} : K.Cut}
  cut_solid(s, "", [], e, {==})

# LAW: the fields of a hub import line from `import` on are `import`, the
# path, `as` and the name
law core_fields:
  for +o: Laws.Gap
  for +os: List<&2, Laws.Gap>
  for +hash: String
  for +path: String
  for +w: Laws.Gap
  for +ws: List<&2, Laws.Gap>
  for +r: Laws.Gap
  for +rs: List<&2, Laws.Gap>
  for +n: Char
  for +ns: String
  for hs: {Laws.solid(hash) == True{} : Bool}
  for pp: {Laws.solid(path) == True{} : Bool}
  for np: {Laws.solid(SCon{n, ns}) == True{} : Bool}
  {K.fields(line.core(o, os, hash, path, w, ws, r, rs, n, ns))
    == ["import", "0x" ++ (hash ++ SCon{'/', path}), "as", SCon{n, ns}]
    : List<&2, String>}

def core_fields(o, os, hash, path, w, ws, r, rs, n, ns, hs, pp, np):
  %Equal.sym(K.Cut, K.cut(line.core(o, os, hash, path, w, ws, r, rs, n, ns)),
    K.Cut{"import", ["0x" ++ (hash ++ SCon{'/', path}), "as", SCon{n, ns}]},
    cut_solid("import", Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})))),
      ["0x" ++ (hash ++ SCon{'/', path}), "as", SCon{n, ns}], {==},
    cut_gap(os, o, ("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns}))),
      "0x" ++ (hash ++ SCon{'/', path}), ["as", SCon{n, ns}],
    cut_solid("0x" ++ (hash ++ SCon{'/', path}),
      Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})),
      ["as", SCon{n, ns}], spec.solid(hash, path, hs, pp),
    cut_gap(ws, w, "as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns}), "as", [SCon{n, ns}],
    cut_solid("as", Laws.gap(r <> rs) ++ SCon{n, ns}, [SCon{n, ns}], {==},
    cut_gap(rs, r, SCon{n, ns}, SCon{n, ns}, [],
    cut_one(SCon{n, ns}, np))))))))
    : {K.cut.all(_) == ["import", "0x" ++ (hash ++ SCon{'/', path}), "as", SCon{n, ns}]
      : List<&2, String>}
  {==}

# the classification

# LAW: the gap bend's parser skips after a foreign `import` is skipped here
law fgap:
  for gs: List<&2, Laws.Gap>
  for s: String
  {K.foreign.gap(Laws.gap(gs) ++ s) == K.foreign.gap(s) : String}

def fgap(gs, s):
  match gs:
    case []:
      {==}
    case g <> t:
      match g:
        case Laws.Sp{}:
          fgap(t, s)
        case Laws.Tab{}:
          fgap(t, s)

# LAW: a hub import line from `import` on names its path as a module
law core_stmt:
  for +o: Laws.Gap
  for +os: List<&2, Laws.Gap>
  for +hash: String
  for +path: String
  for +w: Laws.Gap
  for +ws: List<&2, Laws.Gap>
  for +r: Laws.Gap
  for +rs: List<&2, Laws.Gap>
  for +n: Char
  for +ns: String
  for hs: {Laws.solid(hash) == True{} : Bool}
  for pp: {Laws.solid(path) == True{} : Bool}
  for np: {Laws.solid(SCon{n, ns}) == True{} : Bool}
  {K.stmt_of(line.core(o, os, hash, path, w, ws, r, rs, n, ns))
    == K.SMod{"0x" ++ (hash ++ SCon{'/', path})} : K.Stmt}

def core_stmt(o, os, hash, path, w, ws, r, rs, n, ns, hs, pp, np):
  %Equal.sym(String,
    K.foreign.gap(Laws.gap(o <> os) ++ (("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns}))))),
    K.foreign.gap(("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})))),
    fgap(o <> os, ("0x" ++ (hash ++ SCon{'/', path}))
      ++ (Laws.gap(w <> ws) ++ ("as" ++ (Laws.gap(r <> rs) ++ SCon{n, ns})))))
    : {K.stmt_of.foreign(Bool.and(True{}, K.foreign.quoted(_)),
      line.core(o, os, hash, path, w, ws, r, rs, n, ns))
      == K.SMod{"0x" ++ (hash ++ SCon{'/', path})} : K.Stmt}
  %Equal.sym(List<&2, String>, K.fields(line.core(o, os, hash, path, w, ws, r, rs, n, ns)),
    ["import", "0x" ++ (hash ++ SCon{'/', path}), "as", SCon{n, ns}],
    core_fields(o, os, hash, path, w, ws, r, rs, n, ns, hs, pp, np))
    : {K.base_of(_) == K.SMod{"0x" ++ (hash ++ SCon{'/', path})} : K.Stmt}
  {==}

# the package a hub import names

# LAW: the path of a hub import is one `is_hub` answers True for
law spec_hub:
  for +hash: String
  for +path: String
  {K.is_hub("0x" ++ (hash ++ SCon{'/', path})) == True{} : Bool}

def spec_hub(hash, path):
  L1.hub_named(hash, path)

# LAW: one step of the front, with its head decided
law holds_left.step:
  for bb: Bool
  for +t: List<&2, String>
  for +q: List<&2, String>
  for +x: String
  for e: {L.any.step(bb, _u => L.seen.holds(t, x)) == True{} : Bool}
  for ih: {L.seen.holds(t, x) == True{} : Bool}
    -> {L.seen.holds(List.append(&2, String, t, q), x) == True{} : Bool}
  {L.any.step(bb, _u => L.seen.holds(List.append(&2, String, t, q), x)) == True{} : Bool}

def holds_left.step(bb, _t, _q, _x, e, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih(e)

# LAW: and what its front holds, with anything after it
law holds_left:
  for p: List<&2, String>
  for +q: List<&2, String>
  for +x: String
  for e: {L.seen.holds(p, x) == True{} : Bool}
  {L.seen.holds(List.append(&2, String, p, q), x) == True{} : Bool}

def holds_left(p, q, x, e):
  match p:
    case []:
      Eq.bit.absurd(&2, {L.seen.holds(List.append(&2, String, [], q), x) == True{} : Bool}, e)
    case +y <> +t:
      holds_left.step(String.eq(y, x), t, q, x, e, z => holds_left(t, q, x, z))

# LAW: one step of the front that does not hold it, with its head decided
law holds_back.step:
  for bb: Bool
  for +t: List<&2, String>
  for +q: List<&2, String>
  for +x: String
  for e: {L.any.step(bb, _u => L.seen.holds(List.append(&2, String, t, q), x)) == True{} : Bool}
  for n: {L.any.step(bb, _u => L.seen.holds(t, x)) == False{} : Bool}
  for ih: {L.seen.holds(List.append(&2, String, t, q), x) == True{} : Bool}
    -> {L.seen.holds(t, x) == False{} : Bool}
    -> {L.seen.holds(q, x) == True{} : Bool}
  {L.seen.holds(q, x) == True{} : Bool}

def holds_back.step(bb, _t, _q, _x, e, n, ih):
  match bb:
    case True{}:
      Eq.bit.absurd2(&2, {L.seen.holds(_q, _x) == True{} : Bool}, n)
    case False{}:
      ih(e, n)

# LAW: what a joined list holds and its front does not, its back holds
law holds_back:
  for p: List<&2, String>
  for +q: List<&2, String>
  for +x: String
  for e: {L.seen.holds(List.append(&2, String, p, q), x) == True{} : Bool}
  for n: {L.seen.holds(p, x) == False{} : Bool}
  {L.seen.holds(q, x) == True{} : Bool}

def holds_back(p, q, x, e, n):
  match p:
    case []:
      e
    case +y <> +t:
      holds_back.step(String.eq(y, x), t, q, x, e, n, a => b => holds_back(t, q, x, a, b))

# LAW: what the packages of a list hold, they hold reversed onto anything
law rev_acc:
  for ms: List<&2, String>
  for +acc: List<&2, String>
  for +x: String
  for e: {L.seen.holds(L.specs(acc), x) == True{} : Bool}
  {L.seen.holds(L.specs(List.reverse.go(&2, String, ms, acc)), x) == True{} : Bool}

def rev_acc(ms, acc, x, e):
  match ms:
    case []:
      e
    case +y <> +t:
      rev_acc(t, y <> acc, x, M2.holds_right(L.spec.put(y), L.specs(acc), x, e))

# LAW: one step of the reversal, with whether its head's package is the one
# looked for decided
law rev_has.arm:
  for bb: Bool
  for +y: String
  for +t: List<&2, String>
  for +acc: List<&2, String>
  for +x: String
  for eb: {L.seen.holds(L.spec.put(y), x) == bb : Bool}
  for e: {L.seen.holds(L.specs(y <> t), x) == True{} : Bool}
  for ih: {L.seen.holds(L.specs(t), x) == True{} : Bool}
    -> {L.seen.holds(L.specs(List.reverse.go(&2, String, t, y <> acc)), x) == True{} : Bool}
  {L.seen.holds(L.specs(List.reverse.go(&2, String, t, y <> acc)), x) == True{} : Bool}

def rev_has.arm(bb, y, t, acc, x, eb, e, ih):
  match bb:
    case True{}:
      rev_acc(t, y <> acc, x, holds_left(L.spec.put(y), L.specs(acc), x, eb))
    case False{}:
      ih(holds_back(L.spec.put(y), L.specs(t), x, e, eb))

# LAW: what the packages of a list hold, they hold reversed
law rev_has:
  for ms: List<&2, String>
  for +acc: List<&2, String>
  for +x: String
  for e: {L.seen.holds(L.specs(ms), x) == True{} : Bool}
  {L.seen.holds(L.specs(List.reverse.go(&2, String, ms, acc)), x) == True{} : Bool}

def rev_has(ms, acc, x, e):
  match ms:
    case []:
      Eq.bit.absurd(&2,
        {L.seen.holds(L.specs(List.reverse.go(&2, String, [], acc)), x) == True{} : Bool}, e)
    case +y <> +t:
      rev_has.arm(L.seen.holds(L.spec.put(y), x), y, t, acc, x, {==}, e,
        z => rev_has(t, y <> acc, x, z))

# the scan

# the modules a scan in progress has gathered
def mods.of(st: K.Head) -> List<&2, String>:
  K.Head{_head, ms, _fs} = st
  ms

# LAW: and so for a module, whether the header is open or not
law go_keep.mod:
  for hd: Bool
  for spec: String
  for +ms: List<&2, String>
  for fs: List<&2, String>
  for +x: String
  for e: {L.seen.holds(L.specs(ms), x) == True{} : Bool}
  {L.seen.holds(L.specs(mods.of(K.scan.mod(hd, spec, ms, fs))), x) == True{} : Bool}

def go_keep.mod(hd, spec, ms, _fs, x, e):
  match hd:
    case True{}:
      M2.holds_right(L.spec.put(spec), L.specs(ms), x, e)
    case False{}:
      e

# LAW: and so for a scan in progress taken apart
law go_keep.head:
  for hd: Bool
  for +ms: List<&2, String>
  for fs: List<&2, String>
  for stmt: K.Stmt
  for +x: String
  for e: {L.seen.holds(L.specs(ms), x) == True{} : Bool}
  {L.seen.holds(L.specs(mods.of(K.scan.go(K.Head{hd, ms, fs}, stmt))), x) == True{} : Bool}

def go_keep.head(hd, ms, fs, stmt, x, e):
  match stmt:
    case K.SNone{}:
      e
    case K.SForeign{_at}:
      e
    case K.SBody{}:
      e
    case K.SMod{spec}:
      go_keep.mod(hd, spec, ms, fs, x, e)

# LAW: a line the scan has classified keeps every package it had gathered
law go_keep:
  for st: K.Head
  for stmt: K.Stmt
  for +x: String
  for e: {L.seen.holds(L.specs(mods.of(st)), x) == True{} : Bool}
  {L.seen.holds(L.specs(mods.of(K.scan.go(st, stmt))), x) == True{} : Bool}

def go_keep(st, stmt, x, e):
  match st:
    case K.Head{hd, ms, fs}:
      go_keep.head(hd, ms, fs, stmt, x, e)

# LAW: the lines a scan walks keep every package it had gathered
law walk_keep:
  for ls: List<&2, String>
  for +st: K.Head
  for +x: String
  for e: {L.seen.holds(L.specs(mods.of(st)), x) == True{} : Bool}
  {L.seen.holds(L.specs(mods.of(K.scan.walk(ls, st))), x) == True{} : Bool}

def walk_keep(ls, st, x, e):
  match ls:
    case []:
      e
    case +l <> +t:
      walk_keep(t, K.scan.step(st, l), x, go_keep(st, K.stmt_of(K.trim(l)), x, e))

# LAW: a scan walks the lines of two runs one run after the other
law walk_app:
  for pre: List<&2, String>
  for rest: List<&2, String>
  for st: K.Head
  {K.scan.walk(List.append(&2, String, pre, rest), st)
    == K.scan.walk(rest, K.scan.walk(pre, st)) : K.Head}

def walk_app(pre, rest, st):
  match pre:
    case []:
      {==}
    case +l <> +t:
      walk_app(t, rest, K.scan.step(st, l))

# LAW: what a finished scan's modules name is what it had gathered
law fin_keep:
  for st: K.Head
  for +x: String
  for e: {L.seen.holds(L.specs(mods.of(st)), x) == True{} : Bool}
  {L.seen.holds(L.specs(K.scan.mods(K.scan.fin(st))), x) == True{} : Bool}

def fin_keep(st, x, e):
  match st:
    case K.Head{_hd, ms, _fs}:
      rev_has(ms, [], x, e)

# LAW: a module gathered from a hub import names its package
law mod_names:
  for +hash: String
  for +path: String
  for ms: List<&2, String>
  for hp: {D1.slashless(hash) == True{} : Bool}
  {L.seen.holds(L.specs(("0x" ++ (hash ++ SCon{'/', path})) <> ms), "0x" ++ hash)
    == True{} : Bool}

def mod_names(hash, path, ms, hp):
  %Equal.sym(Bool, K.is_hub("0x" ++ (hash ++ SCon{'/', path})), True{}, spec_hub(hash, path))
    : {L.seen.holds(List.append(&2, String, Bool.pick(List<&2, String>, _,
      [L.spec.hash("0x" ++ (hash ++ SCon{'/', path}))], []), L.specs(ms)), "0x" ++ hash)
      == True{} : Bool}
  %Equal.sym(String, L.spec.hash("0x" ++ (hash ++ SCon{'/', path})), "0x" ++ hash,
    L2.spec_hash("0x" ++ hash, path, hp))
    : {L.seen.holds(_ <> L.specs(ms), "0x" ++ hash) == True{} : Bool}
  %Equal.sym(Bool, String.eq("0x" ++ hash, "0x" ++ hash), True{}, Eq.string_eq_self("0x" ++ hash))
    : {L.any.step(_, _u => L.seen.holds(L.specs(ms), "0x" ++ hash)) == True{} : Bool}
  {==}

def Laws.root_reads_as_bend(
  at,
  text,
  pre,
  post,
  ms,
  fs,
  lead,
  o,
  os,
  hash,
  path,
  w,
  ws,
  r,
  rs,
  n,
  ns,
  tail,
  ez,
  ls,
  hd,
  hp,
  hs,
  pp,
  np
):
  %Equal.sym(Bool, String.starts_with(at, ".ez/"), False{}, ez)
    : {L.seen.holds(Bool.pick(List<&2, String>, _, [], L.specs(K.scan.mods(K.scan(text)))),
      "0x" ++ hash) == True{} : Bool}
  %Equal.sym(List<&2, String>, String.lines(text), List.append(&2, String, pre,
    Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail) <> post), ls)
    : {L.seen.holds(L.specs(K.scan.mods(K.scan.fin(K.scan.walk(_, K.Head{True{}, [], []})))),
      "0x" ++ hash) == True{} : Bool}
  %Equal.sym(K.Head, K.scan.walk(List.append(&2, String, pre,
      Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail) <> post),
      K.Head{True{}, [], []}),
    K.scan.walk(Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail)
      <> post, K.scan.walk(pre, K.Head{True{}, [], []})),
    walk_app(pre, Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail)
      <> post, K.Head{True{}, [], []}))
    : {L.seen.holds(L.specs(K.scan.mods(K.scan.fin(_))), "0x" ++ hash) == True{} : Bool}
  %Equal.sym(K.Head, K.scan.walk(pre, K.Head{True{}, [], []}), K.Head{True{}, ms, fs}, hd)
    : {L.seen.holds(L.specs(K.scan.mods(K.scan.fin(K.scan.walk(
      Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail) <> post,
      _)))), "0x" ++ hash) == True{} : Bool}
  %Equal.sym(String,
    K.trim(Laws.hub.line(lead, o <> os, hash, path, w <> ws, r <> rs, SCon{n, ns}, tail)),
    line.core(o, os, hash, path, w, ws, r, rs, n, ns),
    line_trim(lead, o, os, hash, path, w, ws, r, rs, n, ns, tail, np))
    : {L.seen.holds(L.specs(K.scan.mods(K.scan.fin(K.scan.walk(post,
      K.scan.go(K.Head{True{}, ms, fs}, K.stmt_of(_)))))), "0x" ++ hash) == True{} : Bool}
  %Equal.sym(K.Stmt, K.stmt_of(line.core(o, os, hash, path, w, ws, r, rs, n, ns)),
    K.SMod{"0x" ++ (hash ++ SCon{'/', path})},
    core_stmt(o, os, hash, path, w, ws, r, rs, n, ns, hs, pp, np))
    : {L.seen.holds(L.specs(K.scan.mods(K.scan.fin(K.scan.walk(post,
      K.scan.go(K.Head{True{}, ms, fs}, _))))), "0x" ++ hash) == True{} : Bool}
  fin_keep(K.scan.walk(post, K.Head{True{}, ("0x" ++ (hash ++ SCon{'/', path})) <> ms, fs}),
    "0x" ++ hash,
    walk_keep(post, K.Head{True{}, ("0x" ++ (hash ++ SCon{'/', path})) <> ms, fs}, "0x" ++ hash,
      mod_names(hash, path, ms, hp)))
