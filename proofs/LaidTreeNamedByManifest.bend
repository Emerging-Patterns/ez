# proofs of laws/LaidTreeNamedByManifest.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../src/share/sha.bend as Sha
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/ledger/ignore.bend as I
import ../src/git/git.bend as Git
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/hub/hub.bend as Web
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/LaidTreeNamedByManifest.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1
import ./lemmas/PlanEffectFacts.bend as M2

# LAW: placing found files and weighing laid ones give the same file list:
# each is the found name under the root, with the sha256 of the found text
law placed_is_laid:
  for +pre: String
  for +out: List<&2, K.Hit>
  {K.placed(pre, K.hit.sums(out)) == K.laid.sums(K.laid(pre, out)) : List<&2, K.Item>}

def placed_is_laid(pre, out):
  match out:
    case []:
      {==}
    case K.Hit{+raw, +text} <> t:
      Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
        xs => K.Item{Path.join(pre, raw), Sha.hex(text)} <> xs,
        K.placed(pre, K.hit.sums(t)), K.laid.sums(K.laid(pre, t)),
        placed_is_laid(pre, t))

def Laws.walked_named_by_texts(pre, out):
  Equal.cong(List<&2, K.Item>, String, fs => K.hash_of(fs),
    K.placed(pre, K.hit.sums(out)), K.laid.sums(K.laid(pre, out)),
    placed_is_laid(pre, out))

def Laws.walked_manifest_of_texts(pre, out):
  Equal.cong(List<&2, K.Item>, String, fs => K.manifest_of(fs),
    K.placed(pre, K.hit.sums(out)), K.laid.sums(K.laid(pre, out)),
    placed_is_laid(pre, out))

# whether every verdict is so
def nv.all(js: List<&2, W.Judged>) -> Bool:
  match js:
    case []:
      True{}
    case W.Judged{+h, v} <> t:
      +rest = nv.all(t)
      Bool.and(M1.nv(h, v), rest)

law nv.laid:
  for ok: Bool
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  for e: {String.eq(hash, W.named(W.laid(fs, ss))) == ok : Bool}
  {M1.nv(hash, W.body.laid(ok, hash, fs, ss)) == True{} : Bool}

def nv.laid(ok, _hash, _fs, _ss, e):
  match ok:
    case True{}:
      e
    case False{}:
      {==}

law nv.sums:
  for ok: Bool
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  {M1.nv(hash, W.body.sums(ok, hash, fs, ss)) == True{} : Bool}

def nv.sums(ok, hash, fs, ss):
  match ok:
    case True{}:
      nv.laid(String.eq(hash, W.named(W.laid(fs, ss))), hash, fs, ss, {==})
    case False{}:
      {==}

law nv.escape:
  for clean: Bool
  for +bad: String
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  {M1.nv(hash, W.body.escape.go(clean, bad, hash, fs, ss)) == True{} : Bool}

def nv.escape(clean, _bad, hash, fs, ss):
  match clean:
    case True{}:
      nv.sums(W.sums.ok(fs, ss), hash, fs, ss)
    case False{}:
      {==}

law nv.named:
  for ok: Bool
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.body.named(ok, hash, manifest, ss)) == True{} : Bool}

def nv.named(ok, hash, manifest, ss):
  match ok:
    case True{}:
      nv.escape(String.is_empty(K.escaped(L.manifest.files(String.lines(manifest)))),
        K.escaped(L.manifest.files(String.lines(manifest))), hash,
        L.manifest.files(String.lines(manifest)), ss)
    case False{}:
      {==}

law nv.body:
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.body(hash, manifest, ss)) == True{} : Bool}

def nv.body(hash, manifest, ss):
  nv.named(Web.matches(L.want(hash), manifest), hash, manifest, ss)

law nv.git.body:
  for empty: Bool
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.git.body(empty, hash, manifest, ss)) == True{} : Bool}

def nv.git.body(empty, hash, manifest, ss):
  match empty:
    case True{}:
      {==}
    case False{}:
      nv.body(hash, manifest, ss)

law nv.old:
  for readmeless: Bool
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  {M1.nv(hash, W.git.old(readmeless, hash, fs, ss)) == True{} : Bool}

def nv.old(readmeless, hash, fs, ss):
  match readmeless:
    case True{}:
      nv.git.body(List.is_empty(&2, K.Item, K.readmeless(fs)), hash,
        K.manifest.lines(K.readmeless(fs)), K.readmeless.srcs(fs, ss))
    case False{}:
      nv.git.body(List.is_empty(&2, K.Item, K.bare(K.readmeless(fs))), hash,
        K.manifest.lines(K.bare(K.readmeless(fs))),
        K.bare.srcs(K.readmeless(fs), K.readmeless.srcs(fs, ss)))

law nv.rule:
  for named: Bool
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.git.rule(named, hash, manifest, ss)) == True{} : Bool}

def nv.rule(named, hash, manifest, ss):
  match named:
    case True{}:
      nv.git.body(List.is_empty(&2, K.Item, L.manifest.files(String.lines(manifest))),
        hash, manifest, ss)
    case False{}:
      nv.old(Web.matches(L.want(hash),
          K.manifest.lines(K.readmeless(L.manifest.files(String.lines(manifest))))),
        hash, L.manifest.files(String.lines(manifest)), ss)

law nv.weighed:
  for same: Bool
  for +why: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.git.weighed.go(same, why, hash, manifest, ss)) == True{} : Bool}

def nv.weighed(same, _why, hash, manifest, ss):
  match same:
    case True{}:
      nv.rule(Web.matches(L.want(hash), manifest), hash, manifest, ss)
    case False{}:
      {==}

law nv.git.how:
  for how: W.How
  for +hash: String
  for +url: String
  for +rev: String
  for +nar: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.git.how(how, hash, url, rev, nar, manifest, ss)) == True{} : Bool}

def nv.git.how(how, hash, url, rev, nar, manifest, ss):
  match how:
    case W.Lib{}:
      nv.weighed(String.is_empty(L.nar.why(nar, nar, url, rev)), L.nar.why(nar, nar, url, rev),
        hash, manifest, ss)
    case W.Clone{+got}:
      nv.weighed(String.is_empty(L.nar.why(nar, got, url, rev)), L.nar.why(nar, got, url, rev),
        hash, manifest, ss)
    case W.Served{}:
      {==}

law nv.hub.how:
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.hub.how(how, hash, manifest, ss)) == True{} : Bool}

def nv.hub.how(how, hash, manifest, ss):
  match how:
    case W.Lib{}:
      {==}
    case W.Clone{_got}:
      {==}
    case W.Served{}:
      nv.body(hash, manifest, ss)

law nv.member.how:
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.member.how(how, hash, manifest, ss)) == True{} : Bool}

def nv.member.how(how, hash, manifest, ss):
  match how:
    case W.Lib{}:
      nv.body(hash, manifest, ss)
    case W.Clone{_got}:
      nv.body(hash, manifest, ss)
    case W.Served{}:
      {==}

law nv.src:
  for src: L.Src
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {M1.nv(hash, W.accept.src(src, how, hash, manifest, ss)) == True{} : Bool}

def nv.src(src, how, hash, manifest, ss):
  match src:
    case L.Hub{}:
      nv.hub.how(how, hash, manifest, ss)
    case L.Git{+url, +rev, _entry, _root, +nar, _tag}:
      nv.git.how(how, hash, url, rev, nar, manifest, ss)
    case L.Member{_path, _entry}:
      nv.member.how(how, hash, manifest, ss)

law nv.accept:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for +hash: String
  for a: W.Answer
  {M1.nv(hash, W.accept(orgs, hub, hash, a)) == True{} : Bool}

# LAW: a name's answer lays nothing, whatever the hub said
law nv.said:
  for ok: Bool
  for +name: String
  for +hash: String
  for +hub: String
  {M1.nv(name, W.said.ok(ok, name, hash, hub)) == True{} : Bool}

def nv.said(ok, _name, _hash, _hub):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def nv.accept(orgs, hub, hash, a):
  match a:
    case W.Miss{_why}:
      {==}
    case W.Got{how, +manifest, +ss}:
      nv.src(L.origin(orgs, hash), how, hash, manifest, ss)
    case W.Said{+text}:
      nv.said(L.hash.ok(String.trim(text)), hash, String.trim(text), hub)
    case W.Locked{_text}:
      {==}

law nv.judge:
  for +orgs: List<&2, L.Origin>
  for +hub: String
  for rs: List<&2, W.Reply>
  {nv.all(W.judge(orgs, hub, rs)) == True{} : Bool}

def nv.judge(orgs, hub, rs):
  match rs:
    case []:
      {==}
    case W.Reply{ask, a} <> t:
      %Equal.sym(Bool, M1.nv(W.ask.hash(ask), W.accept(orgs, hub, W.ask.hash(ask), a)), True{},
        nv.accept(orgs, hub, W.ask.hash(ask), a))
        : {Bool.and(_, nv.all(W.judge(orgs, hub, t))) == True{} : Bool}
      nv.judge(orgs, hub, t)

law nv.append:
  for xs: List<&2, W.Judged>
  for +ys: List<&2, W.Judged>
  for +ex: {nv.all(xs) == True{} : Bool}
  for ey: {nv.all(ys) == True{} : Bool}
  {nv.all(List.append(&2, W.Judged, xs, ys)) == True{} : Bool}

def nv.append(xs, ys, ex, ey):
  match xs:
    case []:
      ey
    case W.Judged{+h, +v} <> +t:
      %Equal.sym(Bool, M1.nv(h, v), True{}, Eq.and.left(M1.nv(h, v), nv.all(t), ex))
        : {Bool.and(_, nv.all(List.append(&2, W.Judged, t, ys))) == True{} : Bool}
      nv.append(t, ys, Eq.and.right(M1.nv(h, v), nv.all(t), ex), ey)

law nv.judged:
  for +nx: Up.Next
  for +replies: List<&2, W.Reply>
  {nv.all(W.judged.of(nx, replies)) == True{} : Bool}

def nv.judged(nx, replies):
  nv.append(W.judge(W.next.origins(nx), W.next.hub(nx),
      W.laid.replies(Up.next.trees(nx), W.next.origins(nx), W.next.hub(nx))),
    W.judge(W.next.origins(nx), W.next.hub(nx), replies),
    nv.judge(W.next.origins(nx), W.next.hub(nx),
      W.laid.replies(Up.next.trees(nx), W.next.origins(nx), W.next.hub(nx))),
    nv.judge(W.next.origins(nx), W.next.hub(nx), replies))

# LAW: all but the last of a list with one more at its end is the list
law front_snoc_lock:
  for xs: List<&2, W.Source>
  for x: W.Source
  {P.front(List.append(&2, W.Source, xs, [x])) == xs : List<&2, W.Source>}

def front_snoc_lock(xs, x):
  match xs:
    case []:
      {==}
    case h <> t:
      match t:
        case []:
          {==}
        case h2 <> t2:
          Equal.cong(List<&2, W.Source>, List<&2, W.Source>, ys => h <> ys,
            P.front(List.append(&2, W.Source, h2 <> t2, [x])), h2 <> t2,
            front_snoc_lock(h2 <> t2, x))

# LAW: and the last one's text is its text
law last_snoc:
  for xs: List<&2, W.Source>
  for at: String
  for text: String
  {P.last(List.append(&2, W.Source, xs, [W.Source{at, text}])) == text : String}

def last_snoc(xs, at, text):
  match xs:
    case []:
      {==}
    case _h <> t:
      match t:
        case []:
          {==}
        case h2 <> t2:
          last_snoc(h2 <> t2, at, text)

# LAW: files laid with the manifest of their own texts last are named by
# that manifest when their texts hash to the name
law nv.lay:
  for +h: String
  for +ls: List<&2, W.Source>
  for e: {String.eq(h, W.named(ls)) == True{} : Bool}
  {P.lay.named(h, List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}]))
    == True{} : Bool}

def nv.lay(h, ls, e):
  %Equal.sym(List<&2, W.Source>,
    P.front(List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])), ls,
    front_snoc_lock(ls, W.Source{"manifest", W.manifest(ls)}))
    : {Bool.and(String.eq(h, K.hash_of(K.files_of(W.weighs(_)))),
      String.eq(P.last(List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])),
        K.manifest_of(K.files_of(W.weighs(_))))) == True{} : Bool}
  %Equal.sym(String,
    P.last(List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])),
    W.manifest(ls), last_snoc(ls, "manifest", W.manifest(ls)))
    : {Bool.and(String.eq(h, W.named(ls)), String.eq(_, W.manifest(ls))) == True{} : Bool}
  %Equal.sym(Bool, String.eq(W.manifest(ls), W.manifest(ls)), True{},
    Eq.string_eq_self(W.manifest(ls)))
    : {Bool.and(String.eq(h, W.named(ls)), _) == True{} : Bool}
  %Equal.sym(Bool, String.eq(h, W.named(ls)), True{}, e)
    : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# LAW: a verdict laid in front of trees that are named
law nv.verdict:
  for v: W.Verdict
  for pl: P.Place
  for +h: String
  for +rest: List<&2, P.Effect>
  for ev: {M1.nv(h, v) == True{} : Bool}
  for er: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.lay.verdict(v, pl, h, rest)) == True{} : Bool}

def nv.verdict(v, _pl, h, rest, ev, er):
  match v:
    case W.No{_why}:
      er
    case W.Named{_names}:
      er
    case W.Ok{+fs, +ss}:
      %Equal.sym(Bool, P.lay.named(h, List.append(&2, W.Source, W.laid(fs, ss),
        [W.Source{"manifest", W.manifest(W.laid(fs, ss))}])), True{},
        nv.lay(h, W.laid(fs, ss), ev))
        : {Bool.and(_, P.lays.named(rest)) == True{} : Bool}
      er

# LAW: and when it is one to lay
law nv.pick:
  for b: Bool
  for v: W.Verdict
  for pl: P.Place
  for +h: String
  for +rest: List<&2, P.Effect>
  for ev: {M1.nv(h, v) == True{} : Bool}
  for er: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.lay.pick(b, v, pl, h, rest)) == True{} : Bool}

def nv.pick(b, v, pl, h, rest, ev, er):
  match b:
    case True{}:
      nv.verdict(v, pl, h, rest, ev, er)
    case False{}:
      er

# LAW: every tree the lock lays from verdicts that are named is named
# LAW: a names file laid in front of trees that are named leaves them named:
# it lays no tree
law nv.names:
  for ns: List<&2, L.Name>
  for +rest: List<&2, P.Effect>
  for er: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.names.lay(ns, rest)) == True{} : Bool}

def nv.names(ns, rest, er):
  match ns:
    case []:
      er
    case L.Name{_nv, _hash} <> t:
      nv.names(t, rest, er)

law nv.lays:
  for +cs: List<&2, String>
  for +vs: List<&2, String>
  for js: List<&2, W.Judged>
  for +rest: List<&2, P.Effect>
  for +ej: {nv.all(js) == True{} : Bool}
  for er: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.lays(cs, vs, js, rest)) == True{} : Bool}

def nv.lays(cs, vs, js, rest, ej, er):
  match js:
    case []:
      er
    case W.Judged{+h, +v} <> +t:
      nv.pick(L.seen.holds(cs, h), v, P.place.of(L.seen.holds(vs, h)), h,
        P.lays(cs, vs, t, rest), Eq.and.left(M1.nv(h, v), nv.all(t), ej),
        nv.lays(cs, vs, t, rest, Eq.and.right(M1.nv(h, v), nv.all(t), ej), er))

# LAW: a line a person is told lays nothing
law nv.says:
  for ss: List<&2, String>
  for +rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.says.of(ss, rest)) == True{} : Bool}

def nv.says(ss, rest, e):
  match ss:
    case []:
      e
    case _h <> t:
      nv.says(t, rest, e)

# LAW: nor does a file written
law nv.edits:
  for es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.edits.of(es, rest)) == True{} : Bool}

def nv.edits(es, rest, e):
  match es:
    case []:
      e
    case Up.Edit{_at, _text} <> t:
      nv.edits(t, rest, e)

# LAW: nor a committed tree removed
law nv.drops:
  for ds: List<&2, String>
  for +rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.drops.of(ds, rest)) == True{} : Bool}

def nv.drops(ds, rest, e):
  match ds:
    case []:
      e
    case _h <> t:
      nv.drops(t, rest, e)

# LAW: a plan made from verdicts that are named lays named trees
law nv.made:
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for d: P.Doc
  for ej: {nv.all(js) == True{} : Bool}
  {P.lays.named(P.effects(P.made(nx, cs, js, d))) == True{} : Bool}

def nv.made(nx, cs, js, d, ej):
  match d:
    case P.Doc{+lt}:
      nv.says(Up.next.says(nx), P.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
          P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
            Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))))),
        nv.lays(cs, Up.next.vends(nx), js, P.names.lay(L.names.read(lt),
          P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
            Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])))),
          ej, nv.names(L.names.read(lt),
          P.edits.of(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
            Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]))),
          nv.edits(Up.next.edits(nx), P.edits.of(Up.edit.sources(Up.next.found(nx),
            Up.next.swaps(nx)), P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}])),
            nv.edits(Up.edit.sources(Up.next.found(nx), Up.next.swaps(nx)),
              P.drops.of(Up.next.drops(nx), [P.Write{P.lockfile(), lt}]),
              nv.drops(Up.next.drops(nx), [P.Write{P.lockfile(), lt}], {==}))))))
    case P.Stop{_why}:
      {==}

def Laws.lock_lays_named(w):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      nv.made(W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        nv.judged(W.next(args, ledger, ups), replies))

# LAW: a package the walk judged is its texts' own: the found files placed
# and weighed are the laid ones weighed (`placed_is_laid`)
law fixed_judge:
  for ok: Bool
  for +bad: String
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.judge(ok, bad, root, pre, K.files_of(K.placed(pre, K.hit.sums(out))), out))
    == K.made.judge(ok, bad, root, pre, K.files_of(K.placed(pre, K.hit.sums(out))), out)
    : K.Walked}

def fixed_judge(ok, _bad, root, pre, out):
  match ok:
    case True{}:
      %Equal.sym(List<&2, K.Item>, K.placed(pre, K.hit.sums(out)),
        K.laid.sums(K.laid(pre, out)), placed_is_laid(pre, out))
        : {K.Walked{K.hash_of(K.files_of(K.laid.sums(K.laid(pre, out)))), root, K.laid(pre, out),
          K.files_of(K.laid.sums(K.laid(pre, out)))}
          == K.Walked{K.hash_of(K.files_of(_)), root, K.laid(pre, out), K.files_of(_)}
          : K.Walked}
      {==}
    case False{}:
      {==}

law fixed_placed:
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.placed(root, pre, out)) == K.made.placed(root, pre, out) : K.Walked}

def fixed_placed(root, pre, out):
  fixed_judge(String.is_empty(K.escaped(K.files_of(K.placed(pre, K.hit.sums(out))))),
    K.escaped(K.files_of(K.placed(pre, K.hit.sums(out)))), root, pre, out)

# LAW: a package the license check judged is its texts' own too: a refusal
# names no texts, and a pass is the placed package
law fixed_lic:
  for ok: Bool
  for +bad: String
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.lic(ok, bad, root, pre, out)) == K.made.lic(ok, bad, root, pre, out) : K.Walked}

def fixed_lic(ok, _bad, root, pre, out):
  match ok:
    case True{}:
      fixed_placed(root, pre, out)
    case False{}:
      {==}

law fixed_checked:
  for +root: String
  for +pre: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.checked(root, pre, out)) == K.made.checked(root, pre, out) : K.Walked}

def fixed_checked(root, pre, out):
  fixed_lic(String.is_empty(K.licensed(pre, out)), K.licensed(pre, out), root, pre, out)

law fixed_anc:
  for far: Bool
  for +levels: Nat
  for +dir: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.anc(far, levels, dir, out)) == K.made.anc(far, levels, dir, out) : K.Walked}

def fixed_anc(far, levels, dir, out):
  match far:
    case True{}:
      {==}
    case False{}:
      fixed_checked(Path.climb(levels, dir), Path.tail(dir, levels), out)

law fixed_climb:
  for levels: Nat
  for +dir: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.climb(levels, dir, out)) == K.made.climb(levels, dir, out) : K.Walked}

def fixed_climb(levels, dir, out):
  match levels:
    case 0n:
      fixed_checked(Path.norm(dir), "", out)
    case 1n+ +p:
      fixed_anc(Nat.is_gt((1n + p : Nat), K.comps(dir)), (1n + p : Nat), dir, out)

law fixed_go:
  for stop: K.Stop
  for +entry: String
  for +out: List<&2, K.Hit>
  {M1.fix(K.made.go(stop, entry, out)) == K.made.go(stop, entry, out) : K.Walked}

def fixed_go(stop, entry, out):
  match stop:
    case K.Going{}:
      fixed_climb(K.climb(out), Path.dir(entry), out)
    case K.Missing{_at}:
      {==}
    case K.Climbs{_at}:
      {==}
    case K.Asking{_at}:
      {==}
    case K.Spent{}:
      {==}
    case K.Unnamed{_nv}:
      {==}

law fixed_made:
  for +entry: String
  for st: K.State
  {M1.fix(K.made(entry, st)) == K.made(entry, st) : K.Walked}

def fixed_made(entry, st):
  match st:
    case K.State{_seen, out, stop, _queue}:
      fixed_go(stop, entry, out)

# LAW: a README the walk took along, or one that refused the package, leaves
# the package its texts' own
law fixed_sized:
  for over: Bool
  for +at: String
  for +entry: String
  for text: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  {M1.fix(K.readme.sized(over, at, entry, text, seen, out, queue))
    == K.readme.sized(over, at, entry, text, seen, out, queue) : K.Walked}

def fixed_sized(over, _at, entry, text, seen, out, queue):
  match over:
    case True{}:
      {==}
    case False{}:
      fixed_made(entry, K.State{seen, K.Hit{"README.md", text} <> out, K.Going{}, queue})

# LAW: and so does the README settled, whatever the tree said of it
law fixed_put:
  for got: K.Look
  for +at: String
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  {M1.fix(K.readme.put(got, at, entry, seen, out, queue))
    == K.readme.put(got, at, entry, seen, out, queue) : K.Walked}

def fixed_put(got, at, entry, seen, out, queue):
  match got:
    case K.Here{+text}:
      fixed_sized(K.readme.over(text), at, entry, text, seen, out, queue)
    case K.Absent{}:
      fixed_made(entry, K.State{seen, out, K.Going{}, queue})
    case K.Unasked{}:
      {==}

# LAW: a walk's end judged with its README is its texts' own, however the
# walk ended
law fixed_all_go:
  for stop: K.Stop
  for +tree: K.Tree
  for +entry: String
  for seen: List<&2, String>
  for out: List<&2, K.Hit>
  for queue: List<&2, K.Task>
  {M1.fix(K.made.all.go(stop, tree, entry, seen, out, queue))
    == K.made.all.go(stop, tree, entry, seen, out, queue) : K.Walked}

def fixed_all_go(stop, tree, entry, seen, out, queue):
  match stop:
    case K.Going{}:
      fixed_put(K.find(tree, K.readme(entry)), K.readme(entry), entry, seen, out, queue)
    case K.Missing{at}:
      fixed_made(entry, K.State{seen, out, K.Missing{at}, queue})
    case K.Climbs{at}:
      fixed_made(entry, K.State{seen, out, K.Climbs{at}, queue})
    case K.Asking{at}:
      fixed_made(entry, K.State{seen, out, K.Asking{at}, queue})
    case K.Spent{}:
      fixed_made(entry, K.State{seen, out, K.Spent{}, queue})
    case K.Unnamed{nv}:
      fixed_made(entry, K.State{seen, out, K.Unnamed{nv}, queue})

law fixed_all:
  for +tree: K.Tree
  for +entry: String
  for st: K.State
  {M1.fix(K.made.all(tree, entry, st)) == K.made.all(tree, entry, st) : K.Walked}

def fixed_all(tree, entry, st):
  match st:
    case K.State{seen, out, stop, queue}:
      fixed_all_go(stop, tree, entry, seen, out, queue)

# LAW: the walk of an add is its texts' own
law fixed_walked:
  for +w: A.World
  {M1.fix(AP.walked(w)) == AP.walked(w) : K.Walked}

def fixed_walked(w):
  fixed_all(K.Tree{True{}, AP.files(w), []}, Path.norm(AP.entry(w)), K.walk(AP.fuel(AP.files(w)),
    K.Tree{True{}, AP.files(w), []}, Path.base(Path.norm(AP.entry(w))),
    K.start(Path.norm(AP.entry(w)))))

# LAW: all but the last of a list with one more at its end is the list
law front_snoc_add:
  for xs: List<&2, W.Source>
  for x: W.Source
  {P.front(List.append(&2, W.Source, xs, [x])) == xs : List<&2, W.Source>}

def front_snoc_add(xs, x):
  match xs:
    case []:
      {==}
    case h <> t:
      match t:
        case []:
          {==}
        case h2 <> t2:
          Equal.cong(List<&2, W.Source>, List<&2, W.Source>, ys => h <> ys,
            P.front(List.append(&2, W.Source, h2 <> t2, [x])), h2 <> t2,
            front_snoc_add(h2 <> t2, x))

# LAW: the found files as laid, weighed, are the walk's laid files weighed
law weigh_srcs:
  for fs: List<&2, K.Source>
  {W.weighs(AP.srcs(fs)) == K.laid.sums(fs) : List<&2, K.Item>}

def weigh_srcs(fs):
  match fs:
    case []:
      {==}
    case K.Source{at, text} <> t:
      Equal.cong(List<&2, K.Item>, List<&2, K.Item>, ys => K.Item{at, Sha.hex(text)} <> ys,
        W.weighs(AP.srcs(t)), K.laid.sums(t), weigh_srcs(t))

def lay.files(+fs: List<&2, K.Source>) -> List<&2, W.Source>:
  List.append(&2, W.Source, AP.srcs(fs), [W.Source{"manifest", K.manifest_of(M1.lsum(fs))}])

# LAW: a tree laid from a package's texts, with its manifest last and named
# by its hash, is named
law lay_canon:
  for +fs: List<&2, K.Source>
  {P.lay.named(M1.lh(fs), lay.files(fs)) == True{} : Bool}

def lay_canon(fs):
  %Equal.sym(List<&2, W.Source>, P.front(lay.files(fs)), AP.srcs(fs),
    front_snoc_add(AP.srcs(fs), W.Source{"manifest", K.manifest_of(M1.lsum(fs))}))
    : {Bool.and(String.eq(M1.lh(fs), K.hash_of(K.files_of(W.weighs(_)))),
      String.eq(P.last(lay.files(fs)), K.manifest_of(K.files_of(W.weighs(_))))) == True{}
      : Bool}
  %Equal.sym(List<&2, K.Item>, W.weighs(AP.srcs(fs)), K.laid.sums(fs), weigh_srcs(fs))
    : {Bool.and(String.eq(M1.lh(fs), K.hash_of(K.files_of(_))),
      String.eq(P.last(lay.files(fs)), K.manifest_of(K.files_of(_)))) == True{} : Bool}
  %Equal.sym(String, P.last(lay.files(fs)), K.manifest_of(M1.lsum(fs)),
    last_snoc(AP.srcs(fs), "manifest", K.manifest_of(M1.lsum(fs))))
    : {Bool.and(String.eq(M1.lh(fs), M1.lh(fs)), String.eq(_, K.manifest_of(M1.lsum(fs)))) == True{}
      : Bool}
  %Equal.sym(Bool, String.eq(M1.lh(fs), M1.lh(fs)), True{}, Eq.string_eq_self(M1.lh(fs)))
    : {Bool.and(_, String.eq(K.manifest_of(M1.lsum(fs)), K.manifest_of(M1.lsum(fs)))) == True{}
      : Bool}
  Eq.string_eq_self(K.manifest_of(M1.lsum(fs)))

# LAW: the lines a person is told lay nothing
law says_lays:
  for c: Bool
  for +a: String
  for +b: String
  {P.lays.named(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{b}, P.Say{a}]))
    == True{} : Bool}

def says_lays(c, _a, _b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law drops_lays:
  for gs: List<&2, String>
  for rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(P.drops.of(gs, rest)) == True{} : Bool}

def drops_lays(gs, rest, e):
  match gs:
    case []:
      e
    case _h <> t:
      drops_lays(t, rest, e)

law ignore_lays:
  for b: Bool
  for +next: String
  for gs: List<&2, String>
  for +h: String
  for +a: String
  for +w: A.World
  {P.lays.named(AP.ignore.put(b, next, P.drops.of(gs, AP.says(h, a, w)))) == True{} : Bool}

def ignore_lays(b, _next, gs, h, a, w):
  match b:
    case True{}:
      drops_lays(gs, AP.says(h, a, w), says_lays(String.is_empty(AP.tag(w)),
        Git.import.line(h, a), AP.tag(w) ++ " is " ++ AP.rev(w)))
    case False{}:
      drops_lays(gs, AP.says(h, a, w), says_lays(String.is_empty(AP.tag(w)),
        Git.import.line(h, a), AP.tag(w) ++ " is " ++ AP.rev(w)))

# LAW: the effects of a package made again from its texts lay a named tree
law lays_of:
  for +d: M.Dep
  for +a: String
  for +fs: List<&2, K.Source>
  for +m: M.Manifest
  for +w: A.World
  {P.lays.named(AP.effects.of(d, M1.lh(fs), a, fs, M1.lsum(fs), m, w)) == True{} : Bool}

def lays_of(d, a, fs, m, w):
  M2.both(P.lay.named(M1.lh(fs), lay.files(fs)),
    P.lays.named(AP.ignore.put(String.eq(M1.nxt(d, m, w), A.ignore(w)), M1.nxt(d, m, w),
      P.drops.of(M1.gss(d, M1.lh(fs), m), AP.says(M1.lh(fs), a, w)))),
    lay_canon(fs),
    ignore_lays(String.eq(M1.nxt(d, m, w), A.ignore(w)), M1.nxt(d, m, w), M1.gss(d, M1.lh(fs), m),
      M1.lh(fs), a, w))

law lays_fixed:
  for k: K.Walked
  for +w: A.World
  {P.lays.named(AP.effects.k(M1.fix(k), w)) == True{} : Bool}

def lays_fixed(k, w):
  match k:
    case K.Walked{_h, +r, +fs, _ss}:
      lays_of(AP.dep.of(M1.lh(fs), r, w), AP.at.of(r, w), fs, A.manifest.of(A.read(w)), w)
    case K.Asks{_at}:
      {==}
    case K.Refused{_why}:
      {==}

law lays_walked:
  for +w: A.World
  {P.lays.named(AP.effects.k(AP.walked(w), w)) == True{} : Bool}

def lays_walked(w):
  %fixed_walked(w) : {P.lays.named(AP.effects.k(_, w)) == True{} : Bool}
  lays_fixed(AP.walked(w), w)

law lays_seal:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {P.lays.named(es) == True{} : Bool}
  {P.lays.named(P.effects(AP.seal(es, o))) == True{} : Bool}

def lays_seal(_es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

law lays_v:
  for v: AP.Verdict
  for +w: A.World
  {P.lays.named(P.effects(AP.plan.v(v, w))) == True{} : Bool}

def lays_v(v, w):
  match v:
    case AP.Go{}:
      lays_seal(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), lays_walked(w))
    case AP.Pending{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

def Laws.add_lays_named(w):
  lays_v(AP.decide(w), w)

# ---------------------------------------------------------------------------
# the trees a hub add lays are named (laws/LaidTreeNamedByManifest.bend)

# whether a verdict that has a package has one its files hash to. Proof
# vocabulary.
def hgv(v: H.Verdict) -> Bool:
  match v:
    case H.Go{h, fs, ss}:
      String.eq(h, W.named(W.laid(fs, ss)))
    case H.Pending{_asks}:
      True{}
    case H.Stop{_why}:
      True{}

# whether a lock verdict, laid under a hash, would be named by it, as the
# lock's proofs state it
def lnv(+hash: String, v: W.Verdict) -> Bool:
  match v:
    case W.No{_why}:
      True{}
    case W.Ok{fs, ss}:
      String.eq(hash, W.named(W.laid(fs, ss)))
    case W.Named{_names}:
      True{}

law lnv.laid:
  for ok: Bool
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  for e: {String.eq(hash, W.named(W.laid(fs, ss))) == ok : Bool}
  {lnv(hash, W.body.laid(ok, hash, fs, ss)) == True{} : Bool}

def lnv.laid(ok, _hash, _fs, _ss, e):
  match ok:
    case True{}:
      e
    case False{}:
      {==}

law lnv.sums:
  for ok: Bool
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  {lnv(hash, W.body.sums(ok, hash, fs, ss)) == True{} : Bool}

def lnv.sums(ok, hash, fs, ss):
  match ok:
    case True{}:
      lnv.laid(String.eq(hash, W.named(W.laid(fs, ss))), hash, fs, ss, {==})
    case False{}:
      {==}

law lnv.escape:
  for clean: Bool
  for +bad: String
  for +hash: String
  for +fs: List<&2, K.Item>
  for +ss: List<&2, String>
  {lnv(hash, W.body.escape.go(clean, bad, hash, fs, ss)) == True{} : Bool}

def lnv.escape(clean, _bad, hash, fs, ss):
  match clean:
    case True{}:
      lnv.sums(W.sums.ok(fs, ss), hash, fs, ss)
    case False{}:
      {==}

law lnv.named:
  for ok: Bool
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {lnv(hash, W.body.named(ok, hash, manifest, ss)) == True{} : Bool}

def lnv.named(ok, hash, manifest, ss):
  match ok:
    case True{}:
      lnv.escape(String.is_empty(K.escaped(L.manifest.files(String.lines(manifest)))),
        K.escaped(L.manifest.files(String.lines(manifest))), hash,
        L.manifest.files(String.lines(manifest)), ss)
    case False{}:
      {==}

law lnv.hub.how:
  for how: W.How
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {lnv(hash, W.hub.how(how, hash, manifest, ss)) == True{} : Bool}

def lnv.hub.how(how, hash, manifest, ss):
  match how:
    case W.Lib{}:
      {==}
    case W.Clone{_got}:
      {==}
    case W.Served{}:
      lnv.named(Web.matches(L.want(hash), manifest), hash, manifest, ss)

law hgv_body:
  for vv: W.Verdict
  for +hash: String
  for e: {lnv(hash, vv) == True{} : Bool}
  {hgv(H.decide.body(vv, hash)) == True{} : Bool}

def hgv_body(vv, _hash, e):
  match vv:
    case W.Ok{_fs, _ss}:
      e
    case W.No{_why}:
      {==}
    case W.Named{_ns}:
      {==}

law hgv_got:
  for a: W.Answer
  for +hash: String
  for +w: A.World
  {hgv(H.decide.got(a, hash, w)) == True{} : Bool}

def hgv_got(a, hash, _w):
  match a:
    case W.Got{+how, +manifest, +ss}:
      hgv_body(W.hub.how(how, hash, manifest, ss), hash, lnv.hub.how(how, hash, manifest, ss))
    case W.Miss{_why}:
      {==}
    case W.Said{_text}:
      {==}
    case W.Locked{_text}:
      {==}

law hgv_pkg:
  for g: Maybe<&2, W.Answer>
  for +hash: String
  for +w: A.World
  {hgv(H.decide.pkg(g, hash, w)) == True{} : Bool}

def hgv_pkg(g, hash, w):
  match g:
    case None{}:
      {==}
    case Some{a}:
      hgv_got(a, hash, w)

law hgv_hash:
  for ok: Bool
  for +hash: String
  for +w: A.World
  {hgv(H.decide.hash(ok, hash, w)) == True{} : Bool}

def hgv_hash(ok, hash, w):
  match ok:
    case True{}:
      hgv_pkg(H.heard(A.hubs(w), hash), hash, w)
    case False{}:
      {==}

law hgv_said:
  for a: W.Answer
  for +w: A.World
  {hgv(H.decide.said(a, w)) == True{} : Bool}

def hgv_said(a, w):
  match a:
    case W.Said{+text}:
      hgv_hash(L.hash.ok(String.trim(text)), String.trim(text), w)
    case W.Got{_how, _manifest, _ss}:
      {==}
    case W.Miss{_why}:
      {==}
    case W.Locked{_text}:
      {==}

law hgv_name:
  for g: Maybe<&2, W.Answer>
  for +w: A.World
  {hgv(H.decide.name(g, w)) == True{} : Bool}

def hgv_name(g, w):
  match g:
    case None{}:
      {==}
    case Some{a}:
      hgv_said(a, w)

law hgv_early:
  for b: Bool
  for +why: String
  for +w: A.World
  {hgv(H.decide.early(b, why, w)) == True{} : Bool}

def hgv_early(b, _why, w):
  match b:
    case True{}:
      hgv_name(H.heard(A.hubs(w), A.target(w)), w)
    case False{}:
      {==}

law hgv_read:
  for r: M.Read
  for +w: A.World
  {hgv(H.decide.read(r, w)) == True{} : Bool}

def hgv_read(r, w):
  match r:
    case M.Bad{_why}:
      {==}
    case M.Good{_m}:
      hgv_early(String.is_empty(H.early(w)), H.early(w), w)

# LAW: files laid with the manifest of their own texts last are named by
# that manifest when their texts hash to the name
law hlay:
  for +h: String
  for +ls: List<&2, W.Source>
  for e: {String.eq(h, W.named(ls)) == True{} : Bool}
  {P.lay.named(h, List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}]))
    == True{} : Bool}

def hlay(h, ls, e):
  %Equal.sym(List<&2, W.Source>,
    P.front(List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])), ls,
    front_snoc_add(ls, W.Source{"manifest", W.manifest(ls)}))
    : {Bool.and(String.eq(h, K.hash_of(K.files_of(W.weighs(_)))),
      String.eq(P.last(List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])),
        K.manifest_of(K.files_of(W.weighs(_))))) == True{} : Bool}
  %Equal.sym(String,
    P.last(List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])),
    W.manifest(ls), last_snoc(ls, "manifest", W.manifest(ls)))
    : {Bool.and(String.eq(h, W.named(ls)), String.eq(_, W.manifest(ls))) == True{} : Bool}
  %Equal.sym(Bool, String.eq(W.manifest(ls), W.manifest(ls)), True{},
    Eq.string_eq_self(W.manifest(ls)))
    : {Bool.and(String.eq(h, W.named(ls)), _) == True{} : Bool}
  %Equal.sym(Bool, String.eq(h, W.named(ls)), True{}, e)
    : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# LAW: the lines a hub add tells lay nothing
law hsays_lays:
  for c: Bool
  for +a: String
  for +b: String
  {P.lays.named(Bool.pick(List<&2, P.Effect>, c, [P.Say{a}], [P.Say{a}, P.Say{b}]))
    == True{} : Bool}

def hsays_lays(c, _a, _b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law hignore_lays:
  for b: Bool
  for +next: String
  for +h: String
  for +e: String
  for +w: A.World
  {P.lays.named(H.ignore.put(b, next, H.says(h, e, w))) == True{} : Bool}

def hignore_lays(b, _next, h, e, w):
  match b:
    case True{}:
      hsays_lays(String.is_empty(e), A.target(w) ++ " is " ++ h,
        Git.import.line(A.target(w), Path.norm(e)))
    case False{}:
      hsays_lays(String.is_empty(e), A.target(w) ++ " is " ++ h,
        Git.import.line(A.target(w), Path.norm(e)))

# LAW: a sealed hub plan lays what its effects lay, or nothing
law hseal_lays:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {P.lays.named(es) == True{} : Bool}
  {P.lays.named(P.effects(H.seal(es, o))) == True{} : Bool}

def hseal_lays(_es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

# LAW: the plan for a verdict whose package its files hash to lays named
# trees
law hv_lays:
  for v: H.Verdict
  for +w: A.World
  for g: {hgv(v) == True{} : Bool}
  {P.lays.named(P.effects(H.plan.v(v, w))) == True{} : Bool}

def hv_lays(v, w, g):
  match v:
    case H.Go{+h, +fs, +ss}:
      hseal_lays(H.effects.of(H.dep.of(h, fs, w), h, W.laid(fs, ss),
          A.manifest.of(A.read(w)), w), H.outcome.of(h, fs, w),
        M2.both(P.lay.named(h, List.append(&2, W.Source, W.laid(fs, ss),
            [W.Source{"manifest", W.manifest(W.laid(fs, ss))}])),
          P.lays.named(H.ignore.put(String.eq(I.sync(A.deps.of(Rend.add.keep(
              A.manifest.of(A.read(w)), H.dep.of(h, fs, w))), A.ignore(w)), A.ignore(w)),
            I.sync(A.deps.of(Rend.add.keep(A.manifest.of(A.read(w)), H.dep.of(h, fs, w))),
              A.ignore(w)), H.says(h, H.entry(fs, w), w))),
          hlay(h, W.laid(fs, ss), g),
          hignore_lays(String.eq(I.sync(A.deps.of(Rend.add.keep(A.manifest.of(A.read(w)),
              H.dep.of(h, fs, w))), A.ignore(w)), A.ignore(w)),
            I.sync(A.deps.of(Rend.add.keep(A.manifest.of(A.read(w)), H.dep.of(h, fs, w))),
              A.ignore(w)), h, H.entry(fs, w), w)))
    case H.Pending{_asks}:
      {==}
    case H.Stop{_why}:
      {==}

def Laws.add_named_lays_named(w):
  hv_lays(H.decide(w), w, hgv_read(A.read(w), w))

# ---------------------------------------------------------------------------
# the trees are named

# LAW: the planner weighs a file the way the law vocabulary does
law weighs_same:
  for ls: List<&2, W.Source>
  {FP.weighs(ls) == W.weighs(ls) : List<&2, K.Item>}

def weighs_same(ls):
  match ls:
    case []:
      {==}
    case W.Source{at, text} <> t:
      Equal.cong(List<&2, K.Item>, List<&2, K.Item>, ys => K.Item{at, Sha.hex(text)} <> ys,
        FP.weighs(t), W.weighs(t), weighs_same(t))

law named_seal:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {P.lays.named(es) == True{} : Bool}
  {P.lays.named(FP.effects(FP.seal(es, o))) == True{} : Bool}

def named_seal(_es, o, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

# LAW: files that passed `good`, laid with their manifest last, are named by
# it
law named_got:
  for b: Bool
  for +fs: List<&2, K.Item>
  for +h: String
  for +ls: List<&2, W.Source>
  for rest: List<&2, P.Effect>
  for g: {FP.good(fs, h, ls) == b : Bool}
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(FP.effect.v(FP.judge.got(b, fs, h, ls), rest)) == True{} : Bool}

def named_got(b, fs, h, ls, rest, g, e):
  match b:
    case False{}:
      e
    case True{}:
      %Equal.sym(List<&2, W.Source>,
        P.front(List.append(&2, W.Source, ls, [W.Source{"manifest", FP.manifest(ls)}])),
        ls, front_snoc_add(ls, W.Source{"manifest", FP.manifest(ls)}))
        : {Bool.and(Bool.and(String.eq(h, K.hash_of(K.files_of(W.weighs(_)))),
          String.eq(P.last(List.append(&2, W.Source, ls,
            [W.Source{"manifest", FP.manifest(ls)}])),
            K.manifest_of(K.files_of(W.weighs(_))))), P.lays.named(rest)) == True{}
          : Bool}
      %weighs_same(ls)
        : {Bool.and(Bool.and(String.eq(h, K.hash_of(K.files_of(_))),
          String.eq(P.last(List.append(&2, W.Source, ls,
            [W.Source{"manifest", FP.manifest(ls)}])),
            K.manifest_of(K.files_of(_)))), P.lays.named(rest)) == True{} : Bool}
      %Equal.sym(String,
        P.last(List.append(&2, W.Source, ls, [W.Source{"manifest", FP.manifest(ls)}])),
        FP.manifest(ls), last_snoc(ls, "manifest", FP.manifest(ls)))
        : {Bool.and(Bool.and(String.eq(h, FP.named(ls)), String.eq(_, FP.manifest(ls))),
          P.lays.named(rest)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(FP.manifest(ls), FP.manifest(ls)), True{},
        Eq.string_eq_self(FP.manifest(ls)))
        : {Bool.and(Bool.and(String.eq(h, FP.named(ls)), _), P.lays.named(rest)) == True{}
          : Bool}
      %Equal.sym(Bool, String.eq(h, FP.named(ls)), True{},
        Eq.and.right(FP.paths.safe(ls), String.eq(h, FP.named(ls)),
          Eq.and.right(FP.fits(fs, ls),
            Bool.and(FP.paths.safe(ls), String.eq(h, FP.named(ls))), g)))
        : {Bool.and(Bool.and(_, True{}), P.lays.named(rest)) == True{} : Bool}
      e

law named_one:
  for +fs: List<&2, K.Item>
  for +h: String
  for p: FP.Part
  for rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(FP.effect.v(FP.judge(fs, h, p), rest)) == True{} : Bool}

def named_one(fs, h, p, rest, e):
  match p:
    case FP.AskLaid{}:
      e
    case FP.AskFetch{}:
      e
    case FP.Have{}:
      e
    case FP.Got{+ls}:
      named_got(FP.good(fs, h, ls), fs, h, ls, rest, {==}, e)
    case FP.No{_why}:
      e

law named_all:
  for ps: List<&2, FP.Pt>
  {P.lays.named(FP.effects.of(FP.judged(ps))) == True{} : Bool}

def named_all(ps):
  match ps:
    case []:
      {==}
    case FP.Pt{h, _src, fs, p} <> +t:
      named_one(fs, h, p, FP.effects.of(FP.judged(t)), named_all(t))

# LAW: one names file, in front of trees that are named
law named_put:
  for b: Bool
  for +nv: String
  for +hash: String
  for was: String
  for +rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(FP.name.put.at(b, nv, hash, was, rest)) == True{} : Bool}

def named_put(b, _nv, _hash, _was, _rest, e):
  match b:
    case True{}:
      e
    case False{}:
      e

# LAW: every names file, so
law named_names:
  for ms: List<&2, FP.Nm>
  for +rest: List<&2, P.Effect>
  for e: {P.lays.named(rest) == True{} : Bool}
  {P.lays.named(FP.names.lay(ms, rest)) == True{} : Bool}

def named_names(ms, rest, e):
  match ms:
    case []:
      e
    case m <> +t:
      match m:
        case FP.NmPut{+nv, +hash, +was}:
          named_put(String.is_empty(was), nv, hash, was, FP.names.lay(t, rest),
            named_names(t, rest, e))
        case FP.NmAsk{_nv}:
          named_names(t, rest, e)
        case FP.NmKeep{}:
          named_names(t, rest, e)
        case FP.NmStop{_why}:
          named_names(t, rest, e)

law named_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  {P.lays.named(FP.effects(FP.plan.led(b, g, w))) == True{} : Bool}

def named_led(b, g, w):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          named_seal(FP.names.lay(FP.name.parts.of(F.sects(w), w),
            FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w)))),
            FP.outcome.then(FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
              FP.names.outcome(FP.name.parts.of(F.sects(w), w))),
            named_names(FP.name.parts.of(F.sects(w), w), FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))),
              named_all(FP.parts.of(F.sects(w), w))))

def Laws.fetch_lays_named(w):
  named_led(F.ledger(w), F.lock(w), w)
