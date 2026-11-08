# what each upgrade decision keeps of the ledger it was made from
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/relock/relock.bend as R
import ../../src/lock/plan.bend as P
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/ledger/ignore.bend as I
import ../../src/ledger/upgrade.bend as U
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../laws/GitignoreAllowlistIsLedger.bend as L1
import ../../laws/PathTargetRecordedAsGiven.bend as L2
import ../../laws/defs/LockInputs.bend as D1
import ../../laws/defs/WorldAfterLock.bend as D2
import ./AllowlistBlock.bend as M1
import ./LockPlannerFacts.bend as M2

# The plan's writes. A write to another path leaves a path as it was; the
# upgrade's own files are ez.toml and `.gitignore` alone; and the sources are
# written after them, each once.

# the type that is empty where a path was written
def wrote.emp(w: P.Wrote) -> Type:
  match w:
    case P.Kept{}:
      Unit
    case P.Put{_t}:
      Empty

# LAW: a path left as it was is not a path written
law kept_put_lock:
  for +t: String
  for e: {P.Kept{} == P.Put{t} : P.Wrote}
  Empty

def kept_put_lock(_t, e):
  %e : wrote.emp(_)
  Unit{}

# The upgrade keeps each entry's source
# (laws/PathTargetRecordedAsGiven.bend), and a dependency that does not move
# is left as it was (laws/GitignoreAllowlistIsLedger.bend). A fate that
# becomes an entry keeps the source it was given, and one that did not move
# is the entry it was given; a fate that waits waits with a question; so a
# walk that neither refuses nor waits leaves the ledger's sources in order,
# and leaves the ledger's dependencies as they were when none moved.

# what a dependency that did not move is: the one it was
def st.moved(m: Bool, +d: M.Dep, +h: M.Dep) -> Type:
  match m:
    case True{}:
      Unit
    case False{}:
      {d == h : M.Dep}

# a wait with no question never happens
def st.waits(asks: List<&2, Up.Ask>) -> Type:
  match asks:
    case []:
      Empty
    case _h <> _t:
      Unit

# what one dependency's fate keeps of it
def st.fate(f: Up.Fate, +h: M.Dep) -> Type:
  match f:
    case Up.Became{+d, _o, _n, _p, m, _s, _t}:
      {L2.dep.url(d) == L2.dep.url(h) : String} & st.moved(m, d, h)
    case Up.Waits{asks}:
      st.waits(asks)
    case Up.Halts{_why}:
      Unit

law st.hub:
  for hb: Up.Hubbed
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +hash: String
  for +r: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  for +br: String
  st.fate(Up.dep.hub(hb, M.Dep{hn, hh, he, src}, hash, r, root2, nar2, man, srcs, br),
    M.Dep{hn, hh, he, src})

def st.hub(hb, _hn, _hh, _he, src, _hash, _r, _root2, _nar2, _man, _srcs, _br):
  match hb:
    case Up.Clear{}:
      match src:
        case M.Hub{hv}:
          ({==}, Unit{})
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          ({==}, Unit{})
        case M.Member{mp, mn}:
          ({==}, Unit{})
    case Up.Clash{}:
      Unit{}
    case Up.HubWait{_ask}:
      Unit{}
    case Up.HubNo{_why}:
      Unit{}

law st.adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +r: String
  for +br: String
  st.fate(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, src}, r, br), M.Dep{hn, hh, he, src})

def st.adv(co, rs, hub, hn, hh, he, src, r, br):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      st.hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), hn, hh, he, src,
        Up.hash.of(man), r, root2, nar2, man, srcs, br)
    case Up.CoWait{_ask}:
      Unit{}
    case Up.CoNo{_why}:
      Unit{}

law st.verdict:
  for v: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +br: String
  for +seen: String
  st.fate(Up.dep.verdict(v, rs, hub, M.Dep{hn, hh, he, src}, tip, br, seen),
    M.Dep{hn, hh, he, src})

def st.verdict(v, rs, hub, hn, hh, he, src, _tip, br, _seen):
  match v:
    case U.Keep{}:
      ({==}, {==})
    case U.Drift{}:
      Unit{}
    case U.Off{}:
      Unit{}
    case U.Advance{+rv, _tg}:
      st.adv(Up.checkout(rs, Up.Tree{M.source.url(src), rv, he}), rs, hub, hn, hh, he, src,
        rv, br)

law st.kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  st.fate(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, src}, tip, tg), M.Dep{hn, hh, he, src})

def st.kept(co, rs, hub, hn, hh, he, src, tip, tg):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      st.verdict(U.judge(True{}, True{}, U.agree(hh, Up.hash.kept(hh, man), M.source.nar(src),
        nar2, M.source.root(src), root2), tip, tg), rs, hub, hn, hh, he, src, tip, "",
        Up.hash.kept(hh, man))
    case Up.CoWait{_ask}:
      Unit{}
    case Up.CoNo{_why}:
      Unit{}

law st.onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  for +br: String
  st.fate(Up.dep.onward(a, rs, hub, M.Dep{hn, hh, he, src}, tip, tg, br), M.Dep{hn, hh, he, src})

def st.onward(a, rs, hub, hn, hh, he, src, tip, tg, br):
  match a:
    case Up.Asc{yes}:
      st.verdict(U.judge(False{}, yes, False{}, tip, tg), rs, hub, hn, hh, he, src, tip, br, "")
    case Up.AscWait{_ask}:
      Unit{}
    case Up.AscNo{_why}:
      Unit{}

law st.same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  for +br: String
  st.fate(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, src}, tip, tg, br), M.Dep{hn, hh, he, src})

def st.same(s, rs, hub, hn, hh, he, src, tip, tg, br):
  match s:
    case True{}:
      st.kept(Up.checkout(rs, Up.Tree{M.source.url(src), M.source.rev(src), he}), rs, hub,
        hn, hh, he, src, tip, tg)
    case False{}:
      st.onward(Up.onward(rs, Up.Above{M.source.url(src), M.source.rev(src), tip}), rs, hub,
        hn, hh, he, src, tip, tg, br)

law st.tip:
  for t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  st.fate(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, src}), M.Dep{hn, hh, he, src})

def st.tip(t, rs, hub, hn, hh, he, src):
  match t:
    case Up.At{+tip, +tg, +br}:
      st.same(String.eq(M.source.rev(src), tip), rs, hub, hn, hh, he, src, tip, tg, br)
    case Up.TipWait{_ask}:
      Unit{}
    case Up.TipNo{_why}:
      Unit{}

law st.one:
  for am: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  st.fate(Up.dep.one(am, rs, only, hub, h), h)

def st.one(am, rs, _only, hub, h):
  match am h:
    case U.Hold{} M.Dep{_hn, _hh, _he, _src}:
      ({==}, {==})
    case U.Follow{+ref} M.Dep{+hn, +hh, +he, +src}:
      st.tip(Up.follow(rs, M.source.url(src), ref), rs, hub, hn, hh, he, src)
    case U.Forward{} M.Dep{+hn, +hh, +he, +src}:
      st.tip(Up.forward(rs, M.source.url(src)), rs, hub, hn, hh, he, src)

# what a walk over dependencies that neither refuses nor waits keeps
def st.conc(+ds: List<&2, M.Dep>, +ods: List<&2, M.Dep>, m: Bool) -> Type:
  {L2.dep.urls(ds) == L2.dep.urls(ods) : List<&2, String>} &
    ({m == False{} : Bool} -> {ds == ods : List<&2, M.Dep>})

# what a walk keeps of the dependencies it was given
def st.deps(dd: Up.Deps, +ods: List<&2, M.Dep>) -> Type:
  Up.Deps{+ds, _ss, _es, m, _sy, _tr, asks, bad} = dd
  {asks == [] : List<&2, Up.Ask>} -> {String.is_empty(bad) == True{} : Bool} ->
    st.conc(ds, ods, m)

# LAW: one entry that became one, moved or not, in front of the rest
law st.join.m:
  for m: Bool
  for any: Bool
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for +h: M.Dep
  for +tl: List<&2, M.Dep>
  for sm: st.moved(m, d, h)
  for im: {any == False{} : Bool} -> {ds == tl : List<&2, M.Dep>}
  {Bool.or(m, any) == False{} : Bool} -> {d <> ds == h <> tl : List<&2, M.Dep>}

def st.join.m(m, _any, d, ds, h, tl, sm, im):
  match m:
    case True{}:
      e => Eq.bit.absurd2(&2, {d <> ds == h <> tl : List<&2, M.Dep>}, e)
    case False{}:
      e => Equal.trans(List<&2, M.Dep>, d <> ds, h <> ds, h <> tl,
        Equal.cong(M.Dep, List<&2, M.Dep>, x => x <> ds, d, h, sm),
        Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>, xs => h <> xs, ds, tl, im(e)))

# LAW: the entry and what the rest keeps, together
law st.join.pair:
  for m: Bool
  for any: Bool
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for +h: M.Dep
  for +tl: List<&2, M.Dep>
  for sf: {L2.dep.url(d) == L2.dep.url(h) : String} & st.moved(m, d, h)
  for ic: st.conc(ds, tl, any)
  st.conc(d <> ds, h <> tl, Bool.or(m, any))

def st.join.pair(m, any, d, ds, h, tl, sf, ic):
  (su, sm) = sf
  (iu, im) = ic
  (Equal.trans(List<&2, String>, L2.dep.url(d) <> L2.dep.urls(ds),
      L2.dep.url(h) <> L2.dep.urls(ds), L2.dep.url(h) <> L2.dep.urls(tl),
      Equal.cong(String, List<&2, String>, x => x <> L2.dep.urls(ds), L2.dep.url(d),
        L2.dep.url(h), su),
      Equal.cong(List<&2, String>, List<&2, String>, xs => L2.dep.url(h) <> xs,
        L2.dep.urls(ds), L2.dep.urls(tl), iu)),
    st.join.m(m, any, d, ds, h, tl, sm, im))

law st.join.became:
  for m: Bool
  for any: Bool
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for +h: M.Dep
  for +tl: List<&2, M.Dep>
  for asks: List<&2, Up.Ask>
  for +bad: String
  for sf: {L2.dep.url(d) == L2.dep.url(h) : String} & st.moved(m, d, h)
  for ih: {asks == [] : List<&2, Up.Ask>} -> {String.is_empty(bad) == True{} : Bool} ->
    st.conc(ds, tl, any)
  {asks == [] : List<&2, Up.Ask>} -> {String.is_empty(bad) == True{} : Bool} ->
    st.conc(d <> ds, h <> tl, Bool.or(m, any))

def st.join.became(m, any, d, ds, h, tl, _asks, _bad, sf, ih):
  ea => eb => st.join.pair(m, any, d, ds, h, tl, sf, ih(ea)(eb))

law st.join.waits:
  for more: List<&2, Up.Ask>
  for +asks: List<&2, Up.Ask>
  for +bad: String
  for +ds: List<&2, M.Dep>
  for +ods: List<&2, M.Dep>
  for any: Bool
  for sw: st.waits(more)
  {List.append(&2, Up.Ask, more, asks) == [] : List<&2, Up.Ask>} ->
    {String.is_empty(bad) == True{} : Bool} -> st.conc(ds, ods, any)

def st.join.waits(more, asks, bad, ds, ods, any, sw):
  match more:
    case []:
      Empty.absurd({asks == [] : List<&2, Up.Ask>} -> {String.is_empty(bad) == True{} : Bool} ->
        st.conc(ds, ods, any), sw)
    case +m <> +ms:
      ea => _eb => Eq.bit.absurd(&1, st.conc(ds, ods, any),
        Equal.cong(List<&2, Up.Ask>, Bool, xs => List.is_empty(&2, Up.Ask, xs),
          m <> List.append(&2, Up.Ask, ms, asks), [], ea))

law st.join:
  for f: Up.Fate
  for rest: Up.Deps
  for +h: M.Dep
  for +tl: List<&2, M.Dep>
  for sf: st.fate(f, h)
  for ih: st.deps(rest, tl)
  st.deps(Up.deps.join(f, rest), h <> tl)

def st.join(f, rest, h, tl, sf, ih):
  match f rest:
    case Up.Became{+d, +o, +n, +p, m, _says, _trees} Up.Deps{+ds, _ss, _es, any, _sy, _tr, asks, +bad}:
      st.join.became(m, any, d, ds, h, tl, asks, bad, sf, ih)
    case Up.Waits{more} Up.Deps{+ds, _ss, _es, any, _sy, _tr, +asks, +bad}:
      st.join.waits(more, asks, bad, ds, h <> tl, any, sf)
    case Up.Halts{+why} Up.Deps{+ds, _ss, _es, any, _sy, _tr, _asks, _bad}:
      _ea => eb => Eq.bit.absurd(&1, st.conc(ds, h <> tl, any),
        Equal.trans(Bool, False{}, String.is_empty(Up.halt.why(why)), True{},
          Equal.sym(Bool, String.is_empty(Up.halt.why(why)), False{}, M2.mv.halt_ne(why)), eb))

# LAW: the walk over the ledger's dependencies keeps them so
law st.walk:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for ods: List<&2, M.Dep>
  st.deps(Up.deps.walk(rs, only, hub, ods), ods)

def st.walk(rs, only, hub, ods):
  match ods:
    case []:
      _ea => _eb => ({==}, _e => {==})
    case +h <> +tl:
      st.join(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, tl), h, tl,
        st.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        st.walk(rs, only, hub, tl))

# what one tool pin's fate keeps of it: its source
def st.pin(p: Up.Pinned, +h: M.Cli) -> Type:
  match p:
    case Up.Pinned{t, _m, _s}:
      {L2.tool.url(t) == L2.tool.url(h) : String}
    case Up.PinWait{asks}:
      st.waits(asks)
    case Up.PinHalt{_why}:
      Unit

# LAW: a commit and a NAR hash written into a pin keep its source
law st.set:
  for t: M.Cli
  for +rev: String
  for +tag: String
  for +nar: String
  {L2.tool.url(Up.set(t, rev, tag, nar)) == L2.tool.url(t) : String}

def st.set(t, _rev, _tag, _nar):
  match t:
    case M.Cli{_n, _e, _b, s}:
      match s:
        case M.Hub{hv}:
          {==}
        case M.Git{_url, _r, _g, _root, _nr, _v}:
          {==}
        case M.Member{mp, mn}:
          {==}

law st.tpin:
  for short: Bool
  for +t: M.Cli
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  st.pin(Up.tool.pin(short, t, rev, tag, nar, says), t)

def st.tpin(short, t, rev, tag, nar, _says):
  match short:
    case True{}:
      Unit{}
    case False{}:
      st.set(t, rev, tag, nar)

law st.tweighed:
  for wd: Up.Wd
  for +t: M.Cli
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  st.pin(Up.tool.weighed(wd, t, rev, tag, says), t)

def st.tweighed(wd, t, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      st.tpin(Bool.or(String.is_empty(rev), String.is_empty(nar)), t, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      Unit{}
    case Up.WdNo{_why}:
      Unit{}

law st.tresolved:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +ref: String
  st.pin(Up.tool.resolved(tip, rs, t, ref), t)

def st.tresolved(tip, rs, t, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      st.tweighed(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(t)), rev}), t, rev, ref, [])
    case Up.TipWait{_ask}:
      Unit{}
    case Up.TipNo{_why}:
      Unit{}

law st.tnamed:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +url: String
  st.pin(Up.tool.named(named, rs, t, url), t)

def st.tnamed(named, rs, t, url):
  match named:
    case Up.Named{+ref}:
      st.tresolved(Up.follow(rs, url, ref), rs, t, ref)
    case Up.NamedWait{_ask}:
      Unit{}
    case Up.NamedNo{_why}:
      Unit{}

law st.tverdict:
  for v: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +tip: String
  for +branch: String
  st.pin(Up.tool.verdict(v, rs, t, tip, branch), t)

def st.tverdict(v, rs, t, _tip, branch):
  match v:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      Unit{}
    case U.Off{}:
      Unit{}
    case U.Advance{+rev, _tag}:
      st.tweighed(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(t)), rev}), t, rev, "",
        [Up.say.move(M.tool.name(t), M.source.rev(M.tool.source(t)), rev, branch)])

law st.tnar:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +tip: String
  for +tag: String
  for +nar: String
  st.pin(Up.tool.kept.nar(fill, rs, t, tip, tag, nar), t)

def st.tnar(fill, rs, t, tip, tag, nar):
  match fill:
    case True{}:
      st.tpin(Bool.or(String.is_empty(tip), String.is_empty(nar)), t, tip, "", nar, [])
    case False{}:
      st.tverdict(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(t)), nar), tip,
        tag), rs, t, tip, "")

law st.tkept:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +tip: String
  for +tag: String
  st.pin(Up.tool.kept(wd, rs, t, tip, tag), t)

def st.tkept(wd, rs, t, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      st.tnar(String.is_empty(M.source.nar(M.tool.source(t))), rs, t, tip, tag, nar)
    case Up.WdWait{_ask}:
      Unit{}
    case Up.WdNo{_why}:
      Unit{}

law st.tonward:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  st.pin(Up.tool.onward(asc, rs, t, tip, tag, branch), t)

def st.tonward(asc, rs, t, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      st.tverdict(U.judge(False{}, yes, False{}, tip, tag), rs, t, tip, branch)
    case Up.AscWait{_ask}:
      Unit{}
    case Up.AscNo{_why}:
      Unit{}

law st.tsame:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  st.pin(Up.tool.same(same, rs, t, tip, tag, branch), t)

def st.tsame(same, rs, t, tip, tag, branch):
  match same:
    case True{}:
      st.tkept(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(t)),
        M.source.rev(M.tool.source(t))}), rs, t, tip, tag)
    case False{}:
      st.tonward(Up.onward(rs, Up.Above{M.source.url(M.tool.source(t)),
        M.source.rev(M.tool.source(t)), tip}), rs, t, tip, tag, branch)

law st.ttip:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  st.pin(Up.tool.tip(tip, rs, t), t)

def st.ttip(tip, rs, t):
  match tip:
    case Up.At{+rev, +tag, +branch}:
      st.tsame(String.eq(M.source.rev(M.tool.source(t)), rev), rs, t, rev, tag, branch)
    case Up.TipWait{_ask}:
      Unit{}
    case Up.TipNo{_why}:
      Unit{}

law st.taim:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  st.pin(Up.tool.aim(aim, rs, t), t)

def st.taim(aim, rs, t):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{+ref}:
      st.ttip(Up.follow(rs, M.source.url(M.tool.source(t)), ref), rs, t)
    case U.Forward{}:
      st.ttip(Up.forward(rs, M.source.url(M.tool.source(t))), rs, t)

law st.tfill:
  for noRev: Bool
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  st.pin(Up.tool.fill(noRev, rs, t), t)

def st.tfill(noRev, rs, t):
  match noRev:
    case True{}:
      st.tnamed(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(t))), rs,
        M.source.url(M.tool.source(t)), M.source.tag(M.tool.source(t))), rs, t,
        M.source.url(M.tool.source(t)))
    case False{}:
      st.taim(U.aim(True{}, M.tool.source(t)), rs, t)

law st.tshort:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  st.pin(Up.tool.short(short, rs, t), t)

def st.tshort(short, rs, t):
  match short:
    case True{}:
      st.tfill(String.is_empty(M.source.rev(M.tool.source(t))), rs, t)
    case False{}:
      st.taim(U.aim(True{}, M.tool.source(t)), rs, t)

law st.tgit:
  for g: Bool
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  st.pin(Up.tool.git(g, rs, t), t)

def st.tgit(g, rs, t):
  match g:
    case False{}:
      Unit{}
    case True{}:
      st.tshort(Bool.or(String.is_empty(M.source.rev(M.tool.source(t))),
        String.is_empty(M.source.nar(M.tool.source(t)))), rs, t)

law st.tsel:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +t: M.Cli
  st.pin(Up.tool.sel(sel, rs, t), t)

def st.tsel(sel, rs, t):
  match sel:
    case False{}:
      {==}
    case True{}:
      st.tgit(M.source.is_git(M.tool.source(t)), rs, t)

# what a walk over tool pins keeps of the pins it was given, when it neither
# refuses nor waits: their sources, in order
def st.tconc(+ts: List<&2, M.Cli>, +ots: List<&2, M.Cli>) -> Type:
  {L2.tool.urls(ts) == L2.tool.urls(ots) : List<&2, String>}

def st.tools(tt: Up.Tools, +ots: List<&2, M.Cli>) -> Type:
  Up.Tools{+ts, _m, _sy, asks, bad} = tt
  {asks == [] : List<&2, Up.Ask>} -> {String.is_empty(bad) == True{} : Bool} ->
    st.tconc(ts, ots)

law st.tjoin.waits:
  for more: List<&2, Up.Ask>
  for +asks: List<&2, Up.Ask>
  for +bad: String
  for +ts: List<&2, M.Cli>
  for +ots: List<&2, M.Cli>
  for sw: st.waits(more)
  {List.append(&2, Up.Ask, more, asks) == [] : List<&2, Up.Ask>} ->
    {String.is_empty(bad) == True{} : Bool} -> st.tconc(ts, ots)

def st.tjoin.waits(more, asks, bad, ts, ots, sw):
  match more:
    case []:
      Empty.absurd({asks == [] : List<&2, Up.Ask>} -> {String.is_empty(bad) == True{} : Bool} ->
        st.tconc(ts, ots), sw)
    case +m <> +ms:
      ea => _eb => Eq.bit.absurd(&1, st.tconc(ts, ots),
        Equal.cong(List<&2, Up.Ask>, Bool, xs => List.is_empty(&2, Up.Ask, xs),
          m <> List.append(&2, Up.Ask, ms, asks), [], ea))

law st.tjoin:
  for p: Up.Pinned
  for rest: Up.Tools
  for +h: M.Cli
  for +tl: List<&2, M.Cli>
  for sp: st.pin(p, h)
  for ih: st.tools(rest, tl)
  st.tools(Up.tools.join(p, rest), h <> tl)

def st.tjoin(p, rest, h, tl, sp, ih):
  match p rest:
    case Up.Pinned{+t, _m, _says} Up.Tools{+ts, _any, _sy, asks, +bad}:
      ea => eb => Equal.trans(List<&2, String>, L2.tool.url(t) <> L2.tool.urls(ts),
        L2.tool.url(h) <> L2.tool.urls(ts), L2.tool.url(h) <> L2.tool.urls(tl),
        Equal.cong(String, List<&2, String>, x => x <> L2.tool.urls(ts), L2.tool.url(t),
          L2.tool.url(h), sp),
        Equal.cong(List<&2, String>, List<&2, String>, xs => L2.tool.url(h) <> xs,
          L2.tool.urls(ts), L2.tool.urls(tl), ih(ea)(eb)))
    case Up.PinWait{more} Up.Tools{+ts, _any, _sy, +asks, +bad}:
      st.tjoin.waits(more, asks, bad, ts, h <> tl, sp)
    case Up.PinHalt{+why} Up.Tools{+ts, _any, _sy, _asks, _bad}:
      _ea => eb => Eq.bit.absurd(&1, st.tconc(ts, h <> tl),
        Equal.trans(Bool, False{}, String.is_empty(Up.halt.why(why)), True{},
          Equal.sym(Bool, String.is_empty(Up.halt.why(why)), False{}, M2.mv.halt_ne(why)), eb))

law st.twalk:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for ots: List<&2, M.Cli>
  st.tools(Up.tools.walk(rs, only, ots), ots)

def st.twalk(rs, only, ots):
  match ots:
    case []:
      _ea => _eb => {==}
    case +h <> +tl:
      st.tjoin(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, tl),
        h, tl, st.tsel(U.chosen(only, M.tool.name(h)), rs, h), st.twalk(rs, only, tl))

# What each decision `Up.next` makes keeps
# (laws/PathTargetRecordedAsGiven.bend,
# laws/GitignoreAllowlistIsLedger.bend): the model it renders records the
# sources ez.toml records; and, when it does not stop and read a ledger that
# parsed, it leaves `.gitignore` unwritten only when the file it read is in
# sync with the hashes it commits, and ez.toml unwritten only when those
# hashes are ez.toml's own. The stop reason is carried: every decision but
# the last stops, with a reason that is never empty (`Up.halt.why`), so its
# premise is false.

# what the upgrade's own files say, with what follows them given as `R`
def kp.ven(
  +edits: List<&2, Up.Edit>,
  +vends: List<&2, String>,
  +old: M.Read,
  +ig: String,
  +R: List<&2, P.Effect>
) -> Type:
  ({P.put.in(P.edits.of(edits, R), ".gitignore") == P.Kept{} : P.Wrote} ->
      {Str.clear.all(vends, '\n') == True{} : Bool} ->
        {I.hashes(I.file.lines(ig)) == vends : List<&2, String>}) &
    ({P.put.in(P.edits.of(edits, R), "ez.toml") == P.Kept{} : P.Wrote} ->
      {vends == I.vended(D1.ledger.deps(old)) : List<&2, String>})

# what a decision keeps, over its parts
def kp.parts(
  +model: M.Read,
  +stop: String,
  +read: M.Read,
  +edits: List<&2, Up.Edit>,
  +vends: List<&2, String>,
  +old: M.Read,
  +ig: String,
  +R: List<&2, P.Effect>
) -> Type:
  ({L2.dep.urls(D1.ledger.deps(model)) == L2.dep.urls(D1.ledger.deps(old))
      : List<&2, String>} &
    {L2.tool.urls(L2.ledger.tools(model)) == L2.tool.urls(L2.ledger.tools(old))
      : List<&2, String>}) &
    ({String.is_empty(stop) == True{} : Bool} -> {D1.ledger.good(read) == True{} : Bool} ->
      kp.ven(edits, vends, old, ig, R))

# what a decision keeps of the ledger `old` it was made from
def kp.next(+nx: Up.Next, +old: M.Read, +ig: String, +R: List<&2, P.Effect>) -> Type:
  kp.parts(Up.next.model(nx), Up.next.stop(nx), Up.next.read(nx), Up.next.edits(nx),
    Up.next.vends(nx), old, ig, R)

# what the walks leave, when neither refused nor waited: the sources, and
# the dependencies themselves when none moved
def kp.facts(
  +ds: List<&2, M.Dep>,
  +ts: List<&2, M.Cli>,
  dm: Bool,
  +ods: List<&2, M.Dep>,
  +ots: List<&2, M.Cli>
) -> Type:
  ({L2.dep.urls(ds) == L2.dep.urls(ods) : List<&2, String>} &
    {L2.tool.urls(ts) == L2.tool.urls(ots) : List<&2, String>}) &
    ({dm == False{} : Bool} -> {ds == ods : List<&2, M.Dep>})

# LAW: a decision that stops keeps ez.toml's model, and its premise is false
law kp_stop:
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +why: String
  for asks: List<&2, Up.Ask>
  for +ig: String
  for +R: List<&2, P.Effect>
  kp.next(Up.stopped(M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, why, asks),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, ig, R)

def kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, why, _asks, ig, R):
  (({==}, {==}), es => _eg => Eq.bit.absurd(&1,
    kp.ven([], [], M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, ig, R),
    Equal.trans(Bool, False{}, String.is_empty(Up.halt.why(why)), True{},
      Equal.sym(Bool, String.is_empty(Up.halt.why(why)), False{}, M2.mv.halt_ne(why)), es)))

# LAW: a write to a path leaves the path written, whatever follows
law put_self_kept:
  for +p: String
  for +t: String
  for x: P.Wrote
  for e: {P.put.one(P.Write{p, t}, p, x) == P.Kept{} : P.Wrote}
  Empty

def put_self_kept(p, t, x, e):
  match x:
    case P.Kept{}:
      kept_put_lock(t, Equal.sym(P.Wrote, P.Put{t}, P.Kept{},
        Equal.trans(P.Wrote, P.Put{t}, Bool.pick(P.Wrote, String.eq(p, p), P.Put{t}, P.Kept{}),
          P.Kept{},
          Equal.cong(Bool, P.Wrote, b => Bool.pick(P.Wrote, b, P.Put{t}, P.Kept{}), True{},
            String.eq(p, p), Equal.sym(Bool, String.eq(p, p), True{}, Eq.string_eq_self(p))),
          e)))
    case P.Put{+l}:
      kept_put_lock(l, Equal.sym(P.Wrote, P.Put{l}, P.Kept{}, e))

# LAW: `.gitignore` left unwritten by the allowlist the upgrade made from it
# is in sync with the hashes it commits
law kp_gi:
  for b: Bool
  for +ds: List<&2, M.Dep>
  for +ig: String
  for +R: List<&2, P.Effect>
  for eb: {String.eq(I.sync(ds, ig), ig) == b : Bool}
  for k: {P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R), ".gitignore")
    == P.Kept{} : P.Wrote}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.hashes(I.file.lines(ig)) == I.vended(ds) : List<&2, String>}

def kp_gi(b, ds, ig, R, eb, k, ev):
  match b:
    case True{}:
      %Str.string_eq_true(I.sync(ds, ig), ig, eb)
        : {I.hashes(I.file.lines(_)) == I.vended(ds) : List<&2, String>}
      L1.sync_allowlist_is_the_ledger(ds, ig, ev)
    case False{}:
      Empty.absurd({I.hashes(I.file.lines(ig)) == I.vended(ds) : List<&2, String>},
        put_self_kept(".gitignore", I.sync(ds, ig), P.put.in(R, ".gitignore"), k))

# LAW: the hashes committed when no dependency moved are ez.toml's own
law kp_vend:
  for dm: Bool
  for tm: Bool
  for +ds: List<&2, M.Dep>
  for +ods: List<&2, M.Dep>
  for emv: {Bool.or(dm, tm) == False{} : Bool}
  for hm: {dm == False{} : Bool} -> {ds == ods : List<&2, M.Dep>}
  {I.vended(ds) == I.vended(ods) : List<&2, String>}

def kp_vend(dm, _tm, ds, ods, emv, hm):
  match dm:
    case True{}:
      Eq.bit.absurd2(&2, {I.vended(ds) == I.vended(ods) : List<&2, String>}, emv)
    case False{}:
      Equal.cong(List<&2, M.Dep>, List<&2, String>, x => I.vended(x), ds, ods, hm({==}))

# LAW: the files `Up.done` writes, with whether a pin moved and whether the
# allowlist changed the file given as parameters
law kp_done.arm:
  for moved: Bool
  for +b: Bool
  for dm: Bool
  for tm: Bool
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ig: String
  for +R: List<&2, P.Effect>
  for +eb: {String.eq(I.sync(ds, ig), ig) == b : Bool}
  for emv: {Bool.or(dm, tm) == moved : Bool}
  for hf: kp.facts(ds, ts, dm, ods, ots)
  kp.parts(Up.model.next(moved, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts},
      M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}), Up.fit.why(moved, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds,
        ts}),
    Up.read.next(moved, Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts}),
      M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}),
    Up.edit.toml(moved, Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts}),
      Up.edit.if(b, ".gitignore", I.sync(ds, ig), [])),
    I.vended(ds), M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, ig, R)

def kp_done.arm(
  moved,
  b,
  dm,
  tm,
  pn,
  pe,
  pb,
  hb,
  hbpa,
  hbpv,
  ds,
  ts,
  ods,
  _ots,
  ig,
  R,
  eb,
  emv,
  hf
):
  match moved:
    case True{}:
      (hu, _hm) = hf
      (hu, _es => _eg => (k => ev => kp_gi(b, ds, ig, R, eb,
          Equal.trans(P.Wrote,
            P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R), ".gitignore"),
            P.put.one(P.Write{"ez.toml", Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts})},
              ".gitignore",
              P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R),
                ".gitignore")),
            P.Kept{},
            Equal.sym(P.Wrote,
              P.put.one(P.Write{"ez.toml", Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts})},
                ".gitignore",
                P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R),
                  ".gitignore")),
              P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R),
                ".gitignore"),
              M1.put_one_other("ez.toml", Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts}),
                ".gitignore",
                P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R),
                  ".gitignore"), {==})),
            k), ev),
        k => Empty.absurd({I.vended(ds) == I.vended(ods) : List<&2, String>},
          put_self_kept("ez.toml", Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts}),
            P.put.in(P.edits.of(Up.edit.if(b, ".gitignore", I.sync(ds, ig), []), R), "ez.toml"),
            k))))
    case False{}:
      (_hu, hm) = hf
      (({==}, {==}), _es => _eg => (k => ev => kp_gi(b, ds, ig, R, eb, k, ev),
        _k => kp_vend(dm, tm, ds, ods, emv, hm)))

law kp_done:
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ds: List<&2, M.Dep>
  for ss: List<&2, U.Swap>
  for es: List<&2, U.Swap>
  for +dm: Bool
  for dsy: List<&2, String>
  for dtr: List<&2, Up.Laid>
  for +ts: List<&2, M.Cli>
  for +tm: Bool
  for tsy: List<&2, String>
  for +ig: String
  for fs: List<&2, Up.Found>
  for +R: List<&2, P.Effect>
  for hf: kp.facts(ds, ts, dm, ods, ots)
  kp.next(Up.done(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""},
    Up.Tools{ts, tm, tsy, [], ""}, ig, fs), M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, ig, R)

def kp_done(pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, _ss, _es, dm, _dsy, _dtr, ts, tm, _tsy, ig, _fs, R, hf):
  kp_done.arm(Bool.or(dm, tm), String.eq(I.sync(ds, ig), ig), dm, tm, pn, pe, pb, hb, hbpa, hbpv, ds, ts,
    ods, ots, ig, R, {==}, {==}, hf)

law kp_srcs:
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +ts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +ig: String
  for +R: List<&2, P.Effect>
  for hf: kp.facts(ds, ts, dm, ods, ots)
  kp.next(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots},
    Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}, ig),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, ig, R)

def kp_srcs(srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, ig, R, hf):
  match srcs:
    case Up.Srcs{fs}:
      kp_done(pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, ig, fs, R, hf)
    case Up.SrcsWait{ask}:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, "ez: the upgrade was not given the project's sources",
        [ask], ig, R)
    case Up.SrcsNo{+why}:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, why, [], ig, R)

law kp_ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +ts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +rs: List<&2, Up.Reply>
  for +R: List<&2, P.Effect>
  for e: {Up.text.said(rs, Up.Ignore{}) == said : Up.Said}
  for hf: kp.facts(ds, ts, dm, ods, ots)
  kp.next(Up.got.ignore(said, srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots},
    Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

def kp_ignore(said, srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, rs, R, e, hf):
  match said:
    case Up.Said{+x}:
      %Equal.sym(Up.Said, Up.text.said(rs, Up.Ignore{}), Up.Said{x}, e)
        : kp.next(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots},
          Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}, x),
          M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, D2.ignore.said(_), R)
      kp_srcs(srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, x, R, hf)
    case Up.Unasked{+ask}:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, "ez: the upgrade was not given .gitignore",
        ask <> Up.open.srcs(srcs), D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)
    case Up.Unsaid{+why}:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, why, [], D2.ignore.said(Up.text.said(rs, Up.Ignore{})),
        R)

law kp_asks:
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +ts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +R: List<&2, P.Effect>
  for g: {asks == [] : List<&2, Up.Ask>} -> kp.facts(ds, ts, dm, ods, ots)
  kp.next(Up.pins.asks(asks, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots},
    Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

def kp_asks(asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, R, g):
  match asks:
    case []:
      kp_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""})),
          rs),
        pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, rs, R, {==}, g({==}))
    case +h <> +t:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, "ez: the upgrade still has questions for the remote",
        h <> t, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

law kp_bad:
  for clean: Bool
  for +bad: String
  for asks: List<&2, Up.Ask>
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +ds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dm: Bool
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +ts: List<&2, M.Cli>
  for +tm: Bool
  for +tsy: List<&2, String>
  for +R: List<&2, P.Effect>
  for +dbad: String
  for +tbad: String
  for +ec: {Bool.and(String.is_empty(dbad), String.is_empty(tbad)) == clean : Bool}
  for f: {String.is_empty(dbad) == True{} : Bool} -> {String.is_empty(tbad) == True{} : Bool} ->
    {asks == [] : List<&2, Up.Ask>} -> kp.facts(ds, ts, dm, ods, ots)
  kp.next(Up.pins.bad(clean, bad, asks, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots},
    Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""}),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

def kp_bad(
  clean,
  bad,
  asks,
  rs,
  pn,
  pe,
  pb,
  hb,
  hbpa,
  hbpv,
  ods,
  ots,
  ds,
  ss,
  es,
  dm,
  dsy,
  dtr,
  ts,
  tm,
  tsy,
  R,
  dbad,
  tbad,
  ec,
  f
):
  match clean:
    case True{}:
      kp_asks(asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr, ts, tm, tsy, R,
        f(Eq.and.left(String.is_empty(dbad), String.is_empty(tbad), ec),
          Eq.and.right(String.is_empty(dbad), String.is_empty(tbad), ec)))
    case False{}:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, bad, [], D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

# LAW: questions joined into none are none on the left
law app_nil_l:
  for xs: List<&2, Up.Ask>
  for +ys: List<&2, Up.Ask>
  for e: {List.append(&2, Up.Ask, xs, ys) == [] : List<&2, Up.Ask>}
  {xs == [] : List<&2, Up.Ask>}

def app_nil_l(xs, ys, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Eq.bit.absurd(&2, {h <> t == [] : List<&2, Up.Ask>},
        Equal.cong(List<&2, Up.Ask>, Bool, zs => List.is_empty(&2, Up.Ask, zs),
          h <> List.append(&2, Up.Ask, t, ys), [], e))

# LAW: and on the right
law app_nil_r:
  for xs: List<&2, Up.Ask>
  for +ys: List<&2, Up.Ask>
  for e: {List.append(&2, Up.Ask, xs, ys) == [] : List<&2, Up.Ask>}
  {ys == [] : List<&2, Up.Ask>}

def app_nil_r(xs, ys, e):
  match xs:
    case []:
      e
    case +h <> +t:
      Eq.bit.absurd(&2, {ys == [] : List<&2, Up.Ask>},
        Equal.cong(List<&2, Up.Ask>, Bool, zs => List.is_empty(&2, Up.Ask, zs),
          h <> List.append(&2, Up.Ask, t, ys), [], e))

# LAW: what both walks keep, together
law kp.mk:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for dm: Bool
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for cd: st.conc(ds, ods, dm)
  for ct: st.tconc(ts, ots)
  kp.facts(ds, ts, dm, ods, ots)

def kp.mk(_ds, _ts, _dm, _ods, _ots, cd, ct):
  (cu, cm) = cd
  ((cu, ct), cm)

law kp_pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +R: List<&2, P.Effect>
  for sd: st.deps(dd, ods)
  for stt: st.tools(tt, ots)
  kp.next(Up.pins(dd, tt, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

def kp_pins(dd, tt, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, R, sd, stt):
  match dd tt:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad} Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
      kp_bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
        Bool.pick(String, String.is_empty(dbad), tbad, dbad),
        List.append(&2, Up.Ask, das, tas), rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, ds, ss, es, dm, dsy, dtr,
        ts, tm, tsy, R, dbad, tbad, {==},
        e1 => e2 => +ea => kp.mk(ds, ts, dm, ods, ots, sd(app_nil_l(das, tas, ea))(e1),
          stt(app_nil_r(das, tas, ea))(e2)))

law kp_known:
  for ok: Bool
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for +R: List<&2, P.Effect>
  kp.next(Up.known(ok, only, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}),
    M.Good{M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}}, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

def kp_known(ok, only, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, R):
  match ok:
    case False{}:
      kp_stop(pn, pe, pb, hb, hbpa, hbpv, ods, ots, "ez: no dependency or tool named " ++ only, [],
        D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)
    case True{}:
      kp_pins(Up.deps.walk(rs, only, M.hub.or(hb), ods), Up.tools.walk(rs, only, ots), rs,
        pn, pe, pb, hb, hbpa, hbpv, ods, ots, R, st.walk(rs, only, M.hub.or(hb), ods),
        st.twalk(rs, only, ots))

# LAW: every decision `ez lock --upgrade` makes keeps what `kp.next` says of
# the ledger it read
law kp_next:
  for +only: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  for +R: List<&2, P.Effect>
  kp.next(Up.next(only, r, rs), r, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R)

def kp_next(only, r, rs, R):
  match r:
    case M.Bad{+why}:
      (({==}, {==}), _es => eg => Eq.bit.absurd(&1,
        kp.ven([], [], M.Bad{why}, D2.ignore.said(Up.text.said(rs, Up.Ignore{})), R), eg))
    case M.Good{m}:
      match m:
        case M.Manifest{+pn, +pe, +pb, +hb, +hbpa, +hbpv, +ods, +ots}:
          kp_known(Bool.or(U.known(only, ods), M.tool.known(only, ots)), only, rs, pn, pe, pb, hb, hbpa, hbpv,
            ods, ots, R)
