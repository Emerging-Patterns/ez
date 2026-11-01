# proofs of laws/PathTargetRecordedAsGiven.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/relock/relock.bend as R
import ../src/lock/plan.bend as P
import ../src/pkg/path.bend as Path
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/ez/target.bend as Tgt
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../laws/PathTargetRecordedAsGiven.bend as Laws
import ../laws/WalkPinsLedgerSources.bend as L1
import ../laws/defs/LockInputs.bend as D1
import ../laws/defs/WorldAfterLock.bend as D2
import ./lemmas/AddPlanEffects.bend as M1
import ./lemmas/LockPlannerFacts.bend as M2
import ./lemmas/PlanEffectFacts.bend as M3
import ./lemmas/UpgradeKeeps.bend as M4

# ---------------------------------------------------------------------------
# a source as it was given, and asked anchored
# (laws/PathTargetRecordedAsGiven.bend)

# LAW: every package question asked about a list of hashes is anchored
law an.asks:
  for hs: List<&2, String>
  for +here: String
  for +orgs: List<&2, L.Origin>
  for +hub: String
  {Laws.pkgs.anchored(here, orgs, P.asks.of(hs, here, orgs, hub)) == True{} : Bool}

def an.asks(hs, here, orgs, hub):
  match hs:
    case []:
      {==}
    case +h <> t:
      %Equal.sym(Bool, String.eq(L.src.url(P.anchor.src(here, L.origin(orgs, h))),
        L.src.url(P.anchor.src(here, L.origin(orgs, h)))), True{},
        Eq.string_eq_self(L.src.url(P.anchor.src(here, L.origin(orgs, h)))))
        : {Bool.and(_, Laws.pkgs.anchored(here, orgs, P.asks.of(t, here, orgs, hub))) == True{}
          : Bool}
      an.asks(t, here, orgs, hub)

law an.bad:
  for clean: Bool
  for hs: List<&2, String>
  for +here: String
  for +orgs: List<&2, L.Origin>
  for +hub: String
  {Laws.pkgs.anchored(here, orgs, P.wants.bad(clean, hs, here, orgs, hub)) == True{} : Bool}

def an.bad(clean, hs, here, orgs, hub):
  match clean:
    case True{}:
      an.asks(List.reverse(&2, String, hs), here, orgs, hub)
    case False{}:
      {==}

law an.walk:
  for wk: P.Walk
  for +here: String
  for +orgs: List<&2, L.Origin>
  for +hub: String
  {Laws.pkgs.anchored(here, orgs, P.wants.walk(wk, here, orgs, hub)) == True{} : Bool}

def an.walk(wk, here, orgs, hub):
  match wk:
    case P.Walk{_queue, _packs, hs, +bad}:
      an.bad(String.is_empty(bad), hs, here, orgs, hub)

law an.gap:
  for clean: Bool
  for wk: P.Walk
  for +here: String
  for +orgs: List<&2, L.Origin>
  for +hub: String
  {Laws.pkgs.anchored(here, orgs, P.wants.gap(clean, wk, here, orgs, hub)) == True{} : Bool}

def an.gap(clean, wk, here, orgs, hub):
  match clean:
    case True{}:
      an.walk(wk, here, orgs, hub)
    case False{}:
      {==}

law an.stop:
  for clean: Bool
  for +here: String
  for +led: M.Read
  for listing: W.Listing
  for +js: List<&2, W.Judged>
  {Laws.pkgs.anchored(here, L.ledger.read(led), P.wants.stop(clean, here, led, listing, js))
    == True{} : Bool}

def an.stop(clean, here, led, listing, js):
  match clean:
    case True{}:
      an.gap(String.is_empty(P.need.why(led)), P.walk.of(led, listing, P.table(led, js), js), here,
        L.ledger.read(led), M.hub_of(led))
    case False{}:
      {==}

# LAW: a step that asks about packages asks the ones it was given
law an.pkgs:
  for as: List<&2, W.Ask>
  for names: List<&2, W.Ask>
  for +here: String
  for +orgs: List<&2, L.Origin>
  for +nx: Up.Next
  for listing: W.Listing
  for replies: List<&2, W.Reply>
  for e: {Laws.pkgs.anchored(here, orgs, as) == True{} : Bool}
  {Laws.pkgs.anchored(here, orgs, Laws.step.pkgs(P.step.pkgs(as, names, nx, listing, replies)))
    == True{} : Bool}

def an.pkgs(as, names, _here, _orgs, _nx, _listing, _replies, e):
  match as:
    case []:
      match names:
        case []:
          {==}
        case _n <> _m:
          {==}
    case _h <> _t:
      e

law an.ups:
  for us: List<&2, Up.Ask>
  for +here: String
  for +nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  {Laws.pkgs.anchored(here, W.next.origins(nx),
    Laws.step.pkgs(P.step.ups(us, here, nx, listing, replies))) == True{} : Bool}

def an.ups(us, here, nx, listing, replies):
  match us:
    case []:
      an.pkgs(P.wants.of(here, nx, listing, replies), P.names.wants.of(nx, listing, replies), here,
        W.next.origins(nx), nx, listing, replies,
        an.stop(String.is_empty(Up.next.stop(nx)), here, Up.next.read(nx),
          W.listing.of(nx, listing), P.scan(W.replies.of(nx, replies))))
    case _h <> _t:
      {==}

def Laws.lock_asks_anchored(w):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      an.ups(Up.next.asks(W.next(args, ledger, ups)), W.here.of(args),
        W.next(args, ledger, ups), listing, replies)

# LAW: the questions of queries made from questions are those questions
law an.qasks:
  for as: List<&2, Up.Ask>
  for +here: String
  {Laws.queries.asks(P.queries(here, as)) == as : List<&2, Up.Ask>}

def an.qasks(as, here):
  match as:
    case []:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Up.Ask>, List<&2, Up.Ask>, ys => h <> ys,
        Laws.queries.asks(P.queries(here, t)), t, an.qasks(t, here))

# LAW: and each query asks git its question anchored
law an.qanch:
  for as: List<&2, Up.Ask>
  for +here: String
  {Laws.queries.anchored(here, P.queries(here, as)) == True{} : Bool}

def an.qanch(as, here):
  match as:
    case []:
      {==}
    case +h <> t:
      %Equal.sym(Bool, String.eq(Up.key(Up.anchor(here, h)), Up.key(Up.anchor(here, h))), True{},
        Eq.string_eq_self(Up.key(Up.anchor(here, h))))
        : {Bool.and(_, Laws.queries.anchored(here, P.queries(here, t))) == True{} : Bool}
      an.qanch(t, here)

# LAW: a step that asks about packages puts no query
law an.pkgs.q:
  for as: List<&2, W.Ask>
  for names: List<&2, W.Ask>
  for +nx: Up.Next
  for listing: W.Listing
  for replies: List<&2, W.Reply>
  {Laws.step.queries(P.step.pkgs(as, names, nx, listing, replies)) == [] : List<&2, P.Query>}

def an.pkgs.q(as, names, _nx, _listing, _replies):
  match as:
    case []:
      match names:
        case []:
          {==}
        case _n <> _m:
          {==}
    case _h <> _t:
      {==}

law an.ups.asks:
  for us: List<&2, Up.Ask>
  for +here: String
  for +nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  {Laws.queries.asks(Laws.step.queries(P.step.ups(us, here, nx, listing, replies))) == us
    : List<&2, Up.Ask>}

def an.ups.asks(us, here, nx, listing, replies):
  match us:
    case []:
      Equal.cong(List<&2, P.Query>, List<&2, Up.Ask>, qs => Laws.queries.asks(qs),
        Laws.step.queries(P.step.pkgs(P.wants.of(here, nx, listing, replies),
          P.names.wants.of(nx, listing, replies), nx, listing, replies)), [],
        an.pkgs.q(P.wants.of(here, nx, listing, replies), P.names.wants.of(nx, listing, replies),
          nx, listing, replies))
    case +h <> +t:
      an.qasks(h <> t, here)

law an.ups.anch:
  for us: List<&2, Up.Ask>
  for +here: String
  for +nx: Up.Next
  for +listing: W.Listing
  for +replies: List<&2, W.Reply>
  {Laws.queries.anchored(here, Laws.step.queries(P.step.ups(us, here, nx, listing, replies)))
    == True{} : Bool}

def an.ups.anch(us, here, nx, listing, replies):
  match us:
    case []:
      Equal.cong(List<&2, P.Query>, Bool, qs => Laws.queries.anchored(here, qs),
        Laws.step.queries(P.step.pkgs(P.wants.of(here, nx, listing, replies),
          P.names.wants.of(nx, listing, replies), nx, listing, replies)), [],
        an.pkgs.q(P.wants.of(here, nx, listing, replies), P.names.wants.of(nx, listing, replies),
          nx, listing, replies))
    case +h <> +t:
      an.qanch(h <> t, here)

def Laws.upgrade_asks_its_questions(w):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      an.ups.asks(Up.next.asks(W.next(args, ledger, ups)), W.here.of(args),
        W.next(args, ledger, ups), listing, replies)

def Laws.upgrade_asks_anchored(w):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      an.ups.anch(Up.next.asks(W.next(args, ledger, ups)), W.here.of(args),
        W.next(args, ledger, ups), listing, replies)

# LAW: the packages a walk from the committed sources resolves carry the
# sources the ledger records
law an.recs:
  for +led: M.Read
  for listing: W.Listing
  for +js: List<&2, W.Judged>
  {D1.pinned.all(L.ledger.read(led), P.walk.packs(P.walk.of(led, listing, P.table(led, js), js)))
    == P.walk.packs(P.walk.of(led, listing, P.table(led, js), js)) : List<&2, L.Pack>}

def an.recs(led, listing, js):
  match listing:
    case W.Unlisted{_why}:
      {==}
    case W.Listed{+fs}:
      L1.walk_pins_ledger_sources(
        P.walk.fuel(List.append(&2, String, P.roots(fs), L.name.hashes(P.table(led, js), P.roots.named(fs))),
          P.table(led, js), js),
        L.ledger.read(led), P.table(led, js), js,
        P.Walk{List.append(&2, String, P.roots(fs), L.name.hashes(P.table(led, js), P.roots.named(fs))),
          [], [], ""}, {==})

def Laws.lock_records_as_given(w):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      an.recs(Up.next.read(W.next(args, ledger, ups)),
        W.listing.of(W.next(args, ledger, ups), listing),
        W.judged.of(W.next(args, ledger, ups), replies))

# the dependencies' sources a decision keeps
law kp.durls.of:
  for +nx: Up.Next
  for +old: M.Read
  for +ig: String
  for +R: List<&2, P.Effect>
  for k: M4.kp.next(nx, old, ig, R)
  {Laws.dep.urls(D1.ledger.deps(Up.next.model(nx))) == Laws.dep.urls(D1.ledger.deps(old))
    : List<&2, String>}

def kp.durls.of(_nx, _old, _ig, _R, k):
  (u, _v) = k
  (d, _t) = u
  d

# and the tool pins' sources
law kp.turls.of:
  for +nx: Up.Next
  for +old: M.Read
  for +ig: String
  for +R: List<&2, P.Effect>
  for k: M4.kp.next(nx, old, ig, R)
  {Laws.tool.urls(Laws.ledger.tools(Up.next.model(nx))) == Laws.tool.urls(Laws.ledger.tools(old))
    : List<&2, String>}

def kp.turls.of(_nx, _old, _ig, _R, k):
  (u, _v) = k
  (_d, t) = u
  t

def Laws.upgrade_records_as_given(w):
  match w:
    case W.World{args, +ledger, _listing, _replies, +ups}:
      match args:
        case W.Args{up, +only, _here}:
          match up:
            case False{}:
              {==}
            case True{}:
              kp.durls.of(Up.next(only, W.parsed(ledger), ups), W.parsed(ledger),
                D2.ignore.said(Up.text.said(ups, Up.Ignore{})), [],
                M4.kp_next(only, W.parsed(ledger), ups, []))

def Laws.upgrade_records_tools_as_given(w):
  match w:
    case W.World{args, +ledger, _listing, _replies, +ups}:
      match args:
        case W.Args{up, +only, _here}:
          match up:
            case False{}:
              {==}
            case True{}:
              kp.turls.of(Up.next(only, W.parsed(ledger), ups), W.parsed(ledger),
                D2.ignore.said(Up.text.said(ups, Up.Ignore{})), [],
                M4.kp_next(only, W.parsed(ledger), ups, []))

def Laws.add_records_as_given(w, ok):
  Equal.cong(M.Dep, String, d => M.source.url(M.source.dep(d)), AP.added(w),
    AP.dep.of(M2.wh(AP.walked(w)), M3.wr(AP.walked(w)), w), M1.added_ok(w, ok))

# The target's place is rewritten to the path the premise gives.
def Laws.add_path_as_given(w, p, e):
  %Equal.sym(Tgt.Place, Tgt.classify(A.target(w)), Tgt.Local{p}, e)
    : {A.url.of(_, A.home(w)) == Tgt.expand(A.home(w), p) : String}
  {==}

# ---------------------------------------------------------------------------
# the questions

# LAW: a question about a source names that source
law url_of_ask:
  for q: AP.Q
  for +f: String
  {AP.ask.url(AP.ask.of(q, f)) == f : String}

def url_of_ask(q, _f):
  match q:
    case AP.QTags{}:
      {==}
    case AP.QHead{}:
      {==}
    case AP.QRefs{_ref}:
      {==}
    case AP.QClone{_rev}:
      {==}

# LAW: so every question about a source names it
law from_all:
  for qs: List<&2, AP.Q>
  for +f: String
  {AP.asks.from(AP.asks.of(qs, f), f) == True{} : Bool}

def from_all(qs, f):
  match qs:
    case []:
      {==}
    case h <> t:
      %Equal.sym(Bool, AP.asks.from(AP.asks.of(t, f), f), True{}, from_all(t, f))
        : {Bool.and(String.eq(AP.ask.url(AP.ask.of(h, f)), f), _) == True{} : Bool}
      %Equal.sym(String, AP.ask.url(AP.ask.of(h, f)), f, url_of_ask(h, f))
        : {Bool.and(String.eq(_, f), True{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(f, f), True{}, Eq.string_eq_self(f))
        : {Bool.and(_, True{}) == True{} : Bool}
      {==}

def Laws.add_asks_anchored(w):
  from_all(AP.qs.v(AP.decide(w)), A.from(w))

# ---------------------------------------------------------------------------
# no file is written

law kept_all:
  for vs: List<&2, FP.Verdict>
  for +path: String
  {P.put.in(FP.effects.of(vs), path) == P.Kept{} : P.Wrote}

def kept_all(vs, path):
  match vs:
    case []:
      {==}
    case v <> +t:
      match v:
        case FP.Keep{}:
          kept_all(t, path)
        case FP.Put{_hash, _ls}:
          kept_all(t, path)
        case FP.Stop{_why}:
          kept_all(t, path)

# LAW: one names file writes no path of the project
law kept_put_fetch:
  for b: Bool
  for +nv: String
  for +hash: String
  for was: String
  for +rest: List<&2, P.Effect>
  for +path: String
  for e: {P.put.in(rest, path) == P.Kept{} : P.Wrote}
  {P.put.in(FP.name.put.at(b, nv, hash, was, rest), path) == P.Kept{} : P.Wrote}

def kept_put_fetch(b, _nv, _hash, _was, _rest, _path, e):
  match b:
    case True{}:
      e
    case False{}:
      e

# LAW: and neither does any of them
law kept_names:
  for ms: List<&2, FP.Nm>
  for +rest: List<&2, P.Effect>
  for +path: String
  for e: {P.put.in(rest, path) == P.Kept{} : P.Wrote}
  {P.put.in(FP.names.lay(ms, rest), path) == P.Kept{} : P.Wrote}

def kept_names(ms, rest, path, e):
  match ms:
    case []:
      e
    case m <> +t:
      match m:
        case FP.NmPut{+nv, +hash, +was}:
          kept_put_fetch(String.is_empty(was), nv, hash, was, FP.names.lay(t, rest), path,
            kept_names(t, rest, path, e))
        case FP.NmAsk{_nv}:
          kept_names(t, rest, path, e)
        case FP.NmKeep{}:
          kept_names(t, rest, path, e)
        case FP.NmStop{_why}:
          kept_names(t, rest, path, e)

law kept_seal:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for +path: String
  for e: {P.put.in(es, path) == P.Kept{} : P.Wrote}
  {P.put.plan(FP.seal(es, o), path) == P.Kept{} : P.Wrote}

def kept_seal(_es, o, _path, e):
  match o:
    case P.Success{}:
      e
    case P.Refused{_why}:
      {==}

law kept_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  for +path: String
  {P.put.plan(FP.plan.led(b, g, w), path) == P.Kept{} : P.Wrote}

def kept_led(b, g, w, path):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          kept_seal(FP.names.lay(FP.name.parts.of(F.sects(w), w), FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w)))),
            FP.outcome.then(FP.outcome.of(FP.judged(FP.parts.of(F.sects(w), w))),
              FP.names.outcome(FP.name.parts.of(F.sects(w), w))), path,
            kept_names(FP.name.parts.of(F.sects(w), w), FP.effects.of(FP.judged(FP.parts.of(F.sects(w), w))), path,
              kept_all(FP.judged(FP.parts.of(F.sects(w), w)), path)))

def Laws.fetch_keeps_records(w, path):
  kept_led(F.ledger(w), F.lock(w), w, path)

# ---------------------------------------------------------------------------
# the questions

# LAW: the question that fetches a package asks for it from the source the
# lock records, anchored at `here`
law fetch_ask_anchored:
  for s: L.Src
  for +here: String
  for +hub: String
  for +h: String
  for +ss: List<&2, T.Sect>
  for q: {L.pack.src(L.pack_of(ss, h)) == s : L.Src}
  {FP.ask.anchored(here, L.pack.src(L.pack_of(ss, FP.ask.hash(FP.fetch.ask(s, here, hub, h)))),
    FP.fetch.ask(s, here, hub, h)) == True{} : Bool}

def fetch_ask_anchored(s, here, _hub, h, ss, q):
  match s:
    case L.Hub{}:
      {==}
    case L.Git{url, rev, entry, root, nar, tag}:
      %Equal.sym(L.Src, L.pack.src(L.pack_of(ss, h)), L.Git{url, rev, entry, root, nar, tag}, q)
        : {String.eq(Path.anchor(here, url), Path.anchor(here, L.src.url(_))) == True{} : Bool}
      Eq.string_eq_self(Path.anchor(here, url))
    case L.Member{_path, _entry}:
      {==}

# LAW: so is every question one package asks
law asks_one:
  for +here: String
  for +hub: String
  for +h: String
  for +ss: List<&2, T.Sect>
  for p: FP.Part
  for rest: List<&2, F.Ask>
  for e: {FP.asks.anchored(here, ss, rest) == True{} : Bool}
  {FP.asks.anchored(here, ss,
    FP.ask.pt(FP.Pt{h, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), p}, here, hub, rest))
    == True{} : Bool}

def asks_one(here, hub, h, ss, p, rest, e):
  match p:
    case FP.AskLaid{}:
      e
    case FP.AskFetch{}:
      %Equal.sym(Bool,
        FP.ask.anchored(here,
          L.pack.src(L.pack_of(ss,
            FP.ask.hash(FP.fetch.ask(L.pack.src(L.pack_of(ss, h)), here, hub, h)))),
          FP.fetch.ask(L.pack.src(L.pack_of(ss, h)), here, hub, h)),
        True{},
        fetch_ask_anchored(L.pack.src(L.pack_of(ss, h)), here, hub, h, ss, {==}))
        : {Bool.and(_, FP.asks.anchored(here, ss, rest)) == True{} : Bool}
      e
    case FP.Have{}:
      e
    case FP.Got{_ls}:
      e
    case FP.No{_why}:
      e

# LAW: and so is every question of every package of the lock
law asks_all:
  for +ss: List<&2, T.Sect>
  for +rs: List<&2, F.Reply>
  for +here: String
  for +hub: String
  for hs: List<&2, String>
  {FP.asks.anchored(here, ss, FP.asks.of(FP.parts(ss, rs, here, hub, hs), here, hub))
    == True{} : Bool}

def asks_all(ss, rs, here, hub, hs):
  match hs:
    case []:
      {==}
    case +h <> +t:
      asks_one(here, hub, h, ss,
        FP.weigh.part(FP.weighed(ss, rs, here, h),
          FP.part(rs, L.pack.src(L.pack_of(ss, h)), FP.locked(ss, h), here, hub, h)),
        FP.asks.of(FP.parts(ss, rs, here, hub, t), here, hub),
        asks_all(ss, rs, here, hub, t))

# LAW: the questions of two lists are anchored when each list's are
law asks_app:
  for +here: String
  for +ss: List<&2, T.Sect>
  for xs: List<&2, F.Ask>
  for +ys: List<&2, F.Ask>
  for +ex: {FP.asks.anchored(here, ss, xs) == True{} : Bool}
  for ey: {FP.asks.anchored(here, ss, ys) == True{} : Bool}
  {FP.asks.anchored(here, ss, List.append(&2, F.Ask, xs, ys)) == True{} : Bool}

def asks_app(here, ss, xs, ys, ex, ey):
  match xs:
    case []:
      ey
    case +h <> +t:
      Str.and_true(FP.ask.anchored(here, L.pack.src(L.pack_of(ss, FP.ask.hash(h))), h),
        FP.asks.anchored(here, ss, List.append(&2, F.Ask, t, ys)),
        Eq.and.left(FP.ask.anchored(here, L.pack.src(L.pack_of(ss, FP.ask.hash(h))), h),
          FP.asks.anchored(here, ss, t), ex),
        asks_app(here, ss, t, ys,
          Eq.and.right(FP.ask.anchored(here, L.pack.src(L.pack_of(ss, FP.ask.hash(h))), h),
            FP.asks.anchored(here, ss, t), ex), ey))

# LAW: a names file's question asks no checkout, so it is anchored
law asks_names:
  for +here: String
  for +ss: List<&2, T.Sect>
  for ms: List<&2, FP.Nm>
  {FP.asks.anchored(here, ss, FP.names.asks(ms)) == True{} : Bool}

def asks_names(here, ss, ms):
  match ms:
    case []:
      {==}
    case m <> t:
      match m:
        case FP.NmAsk{_nv}:
          asks_names(here, ss, t)
        case FP.NmKeep{}:
          asks_names(here, ss, t)
        case FP.NmPut{_nv, _hash, _was}:
          asks_names(here, ss, t)
        case FP.NmStop{_why}:
          asks_names(here, ss, t)

law asks_led:
  for b: Bool
  for g: Maybe<&2, String>
  for +w: F.World
  {FP.asks.anchored(F.here(w), F.sects(w), FP.wants.led(b, g, w)) == True{} : Bool}

def asks_led(b, g, w):
  match b:
    case False{}:
      {==}
    case True{}:
      match g:
        case None{}:
          {==}
        case Some{_t}:
          asks_app(F.here(w), F.sects(w),
            FP.asks.of(FP.parts.of(F.sects(w), w), F.here(w), L.lock.hub(F.sects(w))),
            FP.names.asks(FP.name.parts.of(F.sects(w), w)),
            asks_all(F.sects(w), F.replies(w), F.here(w), L.lock.hub(F.sects(w)),
              L.hashes(F.sects(w))),
            asks_names(F.here(w), F.sects(w), FP.name.parts.of(F.sects(w), w)))

def Laws.fetch_asks_anchored(w):
  asks_led(F.ledger(w), F.lock(w), w)

# `://` is found wherever it is put (`contains_url`), and that picks the arm
# that keeps a URL.
def Laws.anchor_url(here, a, b):
  %Equal.sym(Bool, String.contains(a ++ ("://" ++ b), "://"), True{},
    M3.contains_url(a, b)) :
    {Path.anchor.at(_, here, a ++ ("://" ++ b)) == a ++ ("://" ++ b) : String}
  {==}

# `/` in front of anything starts with `/`, which `starts_append` holds, and
# that picks the arm that keeps the path.
def Laws.anchor_absolute(here, rest, e):
  %e : {Path.anchor.at(_, here, "/" ++ rest) == "/" ++ rest : String}
  %Equal.sym(Bool, String.starts_with("/" ++ rest, "/"), True{},
    Eq.starts_append("/", rest)) :
    {Path.anchor.path(Bool.or(_, String.starts_with("/" ++ rest, "git@")), here,
      "/" ++ rest) == "/" ++ rest : String}
  {==}

def Laws.anchor_relative(here, path, eu, ea, eg):
  %eu : {Path.anchor.at(_, here, path) == Path.join(here, path) : String}
  %ea : {Path.anchor.path(Bool.or(_, String.starts_with(path, "git@")), here,
    path) == Path.join(here, path) : String}
  %eg : {Path.anchor.path(_, here, path) == Path.join(here, path) : String}
  {==}
