# what an upgrade writes around the ledger: .gitignore's other lines and its
# own files
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/ledger/ignore.bend as I
import ../../src/ledger/upgrade.bend as U
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../laws/GitignoreAllowlistIsLedger.bend as L1
import ../../laws/defs/LockInputs.bend as D1
import ../../laws/defs/WorldAfterLock.bend as D2
import ./AllowlistBlock.bend as M1
import ./NewlineFreeLines.bend as M2

# LAW: a line the project wrote goes in front whatever follows it
law others_put_app:
  for k: I.Rule
  for +line: String
  for a: List<&2, String>
  for b: List<&2, String>
  {I.others.put(k, line, List.append(&2, String, a, b))
    == List.append(&2, String, I.others.put(k, line, a), b) : List<&2, String>}

def others_put_app(k, _line, _a, _b):
  match k:
    case I.Other{}:
      {==}
    case I.Dir{}:
      {==}
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{x}:
      {==}

# LAW: the project's lines of two runs are the one's then the other's
law others_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {I.others(List.append(&2, String, xs, ys))
    == List.append(&2, String, I.others(xs), I.others(ys)) : List<&2, String>}

def others_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.others.put(I.kind(h), h, I.others(List.append(&2, String, t, ys))),
        I.others.put(I.kind(h), h,
          List.append(&2, String, I.others(t), I.others(ys))),
        List.append(&2, String, I.others.put(I.kind(h), h, I.others(t)),
          I.others(ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          y => I.others.put(I.kind(h), h, y),
          I.others(List.append(&2, String, t, ys)),
          List.append(&2, String, I.others(t), I.others(ys)),
          others_app(t, ys)),
        others_put_app(I.kind(h), h, I.others(t), I.others(ys)))

# LAW: and none of them is the project's
law others_each:
  for +hs: List<&2, String>
  for +e: {M2.full.all(hs) == True{} : Bool}
  {I.others(I.allow.each(hs)) == [] : List<&2, String>}

def others_each(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.others.put(I.kind(I.allow(h)), I.allow(h), I.others(I.allow.each(t))),
        I.others.put(I.Allow{h}, I.allow(h), I.others(I.allow.each(t))),
        [],
        Equal.cong(I.Rule, List<&2, String>,
          r => I.others.put(r, I.allow(h), I.others(I.allow.each(t))),
          I.kind(I.allow(h)), I.Allow{h}, M2.kind_allow(h, M2.full_head(h, t, e))),
        others_each(t, M2.full_tail(h, t, e)))

# LAW: and are ez's, not the project's
law rules_are_ez:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {I.others(I.rules.go(b1, b2, b3)) == [] : List<&2, String>}

def rules_are_ez(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: and add none of the project's lines
law need_others:
  for s: Bool
  for +rs: List<&2, String>
  for h: {I.others(rs) == [] : List<&2, String>}
  {I.others(I.need(s, rs)) == [] : List<&2, String>}

def need_others(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: and none of the project's lines
law block_others:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, I.Line>
  {I.others(I.block(ds, ls)) == [] : List<&2, String>}

def block_others(ds, ls):
  Equal.trans(List<&2, String>,
    I.others(List.append(&2, String,
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds))),
    List.append(&2, String,
      I.others(I.need(Bool.or(I.has(ls, I.Dir{}),
        List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
      I.others(I.allows(ds))),
    [],
    others_app(
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds)),
    Equal.trans(List<&2, String>,
      List.append(&2, String,
        I.others(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        I.others(I.allows(ds))),
      I.others(I.allows(ds)),
      [],
      Equal.cong(List<&2, String>, List<&2, String>,
        y => List.append(&2, String, y, I.others(I.allows(ds))),
        I.others(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        [],
        need_others(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls),
          rules_are_ez(I.has(ls, I.Star{}), I.has(ls, I.Lib{}),
            I.has(ls, I.Pkgs{})))),
      others_each(I.vended(ds), M2.vended_full(ds))))

# LAW: and adds none of the project's lines
law others_placed:
  for +d: Bool
  for +blk: List<&2, String>
  for +ob: {I.others(blk) == [] : List<&2, String>}
  {I.others(I.placed(d, blk)) == [] : List<&2, String>}

def others_placed(d, _blk, ob):
  match d:
    case True{}:
      {==}
    case False{}:
      ob

# LAW: one line of the walk, counted for the project's lines. A kept line
# is the line; a `.ez/` and an allowlist line are ez's, and what replaces
# them is too.
law walk_others.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +of: {I.others(fix) == [] : List<&2, String>}
  for +ob: {I.others(blk) == [] : List<&2, String>}
  for ihd: {I.others(I.walk(I.tag(t), fix, blk, d)) == I.others(t)
    : List<&2, String>}
  for iht: {I.others(I.walk(I.tag(t), fix, blk, True{})) == I.others(t)
    : List<&2, String>}
  {I.others(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d))
    == I.others.put(I.kind(h), h, I.others(t)) : List<&2, String>}

def walk_others.arm(k, h, t, fix, blk, d, ek, of, ob, ihd, iht):
  match k:
    case I.Other{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Star{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Lib{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Pkgs{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Dir{}:
      Equal.trans(List<&2, String>,
        I.others(List.append(&2, String, fix, I.walk(I.tag(t), fix, blk, d))),
        List.append(&2, String, I.others(fix),
          I.others(I.walk(I.tag(t), fix, blk, d))),
        I.others.put(I.kind(h), h, I.others(t)),
        others_app(fix, I.walk(I.tag(t), fix, blk, d)),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.others(fix),
            I.others(I.walk(I.tag(t), fix, blk, d))),
          I.others(I.walk(I.tag(t), fix, blk, d)),
          I.others.put(I.kind(h), h, I.others(t)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, y,
              I.others(I.walk(I.tag(t), fix, blk, d))),
            I.others(fix), [], of),
          Equal.trans(List<&2, String>,
            I.others(I.walk(I.tag(t), fix, blk, d)),
            I.others(t),
            I.others.put(I.kind(h), h, I.others(t)),
            ihd,
            Equal.sym(List<&2, String>,
              I.others.put(I.kind(h), h, I.others(t)), I.others(t),
              Equal.cong(I.Rule, List<&2, String>,
                r => I.others.put(r, h, I.others(t)), I.kind(h), I.Dir{}, ek)))))
    case I.Allow{x}:
      Equal.trans(List<&2, String>,
        I.others(List.append(&2, String, I.placed(d, blk),
          I.walk(I.tag(t), fix, blk, True{}))),
        List.append(&2, String, I.others(I.placed(d, blk)),
          I.others(I.walk(I.tag(t), fix, blk, True{}))),
        I.others.put(I.kind(h), h, I.others(t)),
        others_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{})),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.others(I.placed(d, blk)),
            I.others(I.walk(I.tag(t), fix, blk, True{}))),
          I.others(I.walk(I.tag(t), fix, blk, True{})),
          I.others.put(I.kind(h), h, I.others(t)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, y,
              I.others(I.walk(I.tag(t), fix, blk, True{}))),
            I.others(I.placed(d, blk)), [], others_placed(d, blk, ob)),
          Equal.trans(List<&2, String>,
            I.others(I.walk(I.tag(t), fix, blk, True{})),
            I.others(t),
            I.others.put(I.kind(h), h, I.others(t)),
            iht,
            Equal.sym(List<&2, String>,
              I.others.put(I.kind(h), h, I.others(t)), I.others(t),
              Equal.cong(I.Rule, List<&2, String>,
                r => I.others.put(r, h, I.others(t)), I.kind(h), I.Allow{x},
                ek)))))

# LAW: the walk keeps every line of the project's, in order
law walk_others:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +of: {I.others(fix) == [] : List<&2, String>}
  for +ob: {I.others(blk) == [] : List<&2, String>}
  {I.others(I.walk(I.tag(raw), fix, blk, d)) == I.others(raw)
    : List<&2, String>}

def walk_others(raw, fix, blk, d, of, ob):
  match raw:
    case []:
      others_placed(d, blk, ob)
    case +h <> +t:
      walk_others.arm(I.kind(h), h, t, fix, blk, d, {==}, of, ob,
        walk_others(t, fix, blk, d, of, ob),
        walk_others(t, fix, blk, True{}, of, ob))

# The walk keeps the project's lines, and what it adds is all ez's.
def L1.allowlist_keeps_other_lines(ds, ls):
  walk_others(ls, I.rules(I.tag(ls)), I.block(ds, I.tag(ls)), False{},
    rules_are_ez(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
      I.has(I.tag(ls), I.Pkgs{})),
    block_others(ds, I.tag(ls)))

def L1.sync_keeps_other_lines(ds, text, ev):
  Equal.trans(List<&2, String>,
    I.others(I.file.lines(I.sync(ds, text))),
    I.others(I.lines(ds, I.file.lines(text))),
    I.others(I.file.lines(text)),
    Equal.cong(List<&2, String>, List<&2, String>, y => I.others(y),
      I.file.lines(I.sync(ds, text)), I.lines(ds, I.file.lines(text)),
      M1.sync_lines(ds, text, ev)),
    L1.allowlist_keeps_other_lines(ds, I.file.lines(text)))

# Each hash once. The walk keeps a hash only when it has not seen it, and
# every hash it keeps after that is one it had not seen either, so none of
# them is the hash it kept.

# LAW: the negation of a bit that answered False
law not_of_false:
  for x: Bool
  for e: {x == False{} : Bool}
  {Bool.not(x) == True{} : Bool}

def not_of_false(x, e):
  %Equal.sym(Bool, x, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

# LAW: two strings that compare unequal compare unequal the other way round
law eq_flip:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == False{} : Bool}
  {String.eq(b, a) == False{} : Bool}

# LAW: the same, with how the other comparison went given as a parameter
law eq_flip.arm:
  for +a: String
  for +b: String
  for c: Bool
  for ec: {String.eq(b, a) == c : Bool}
  for e: {String.eq(a, b) == False{} : Bool}
  {String.eq(b, a) == False{} : Bool}

def eq_flip.arm(a, b, c, ec, e):
  match c:
    case False{}:
      ec
    case True{}:
      Eq.bit.absurd(&2, {String.eq(b, a) == False{} : Bool},
        Equal.trans(Bool, False{}, String.eq(a, a), True{},
          Equal.trans(Bool, False{}, String.eq(a, b), String.eq(a, a),
            Equal.sym(Bool, String.eq(a, b), False{}, e),
            Equal.cong(String, Bool, x => String.eq(a, x), b, a,
              Str.string_eq_true(b, a, ec))),
          Eq.string_eq_self(a)))

def eq_flip(a, b, e):
  eq_flip.arm(a, b, String.eq(b, a), {==}, e)

# What an upgrade writes around the ledger
# (laws/GitignoreAllowlistIsLedger.bend, laws/UpgradeRewritesImports.bend,
# laws/RewriteKeepsOtherLines.bend). The upgrade's own files are ez.toml and
# `.gitignore`, and nothing else: each stage of `Up.next` either stops with
# no file or goes on, and the last one, `Up.done`, writes ez.toml over the
# ledger it leaves when a pin moved and `.gitignore` as `I.sync` makes it
# from the file it read. `ok.next` says that of a decision; every decision
# `Up.next` makes is one. The sources are written after them, one write per
# source whose text the moves change, and the lock last.

# what one of the upgrade's own files may be: ez.toml over the ledger the
# model renders, or `.gitignore` with the allowlist of the hashes it commits
# and the lines of the file it read that are not ez's. Law vocabulary: ez
# never calls it.
def ok.go(
  toml: Bool,
  gi: Bool,
  +t: String,
  +vs: List<&2, String>,
  model: M.Read,
  +ig: String
) -> Type:
  match toml gi:
    case True{} _:
      {vs == I.vended(D1.ledger.deps(model)) : List<&2, String>}
    case False{} True{}:
      {Str.clear.all(vs, '\n') == True{} : Bool} ->
        ({I.hashes(I.file.lines(t)) == vs : List<&2, String>} &
          {I.others(I.file.lines(t)) == I.others(I.file.lines(ig)) : List<&2, String>})
    case False{} False{}:
      Empty

# one file the upgrade writes, so
def ok.edit(e: Up.Edit, +vs: List<&2, String>, +model: M.Read, +ig: String) -> Type:
  Up.Edit{+p, t} = e
  ok.go(String.eq(p, "ez.toml"), String.eq(p, ".gitignore"), t, vs, model, ig)

# every file the upgrade writes, so
def ok.edits(es: List<&2, Up.Edit>, +vs: List<&2, String>, +model: M.Read, +ig: String) -> Type:
  match es:
    case []:
      Unit
    case e <> t:
      ok.edit(e, vs, model, ig) & ok.edits(t, vs, model, ig)

# what the upgrade decided, over `.gitignore` as it read it
def ok.next(+nx: Up.Next, +ig: String) -> Type:
  ok.edits(Up.next.edits(nx), Up.next.vends(nx), Up.next.model(nx), ig)

# LAW: the files `Up.done` writes, with whether a pin moved and whether the
# allowlist changed the file given as parameters
law ok_done.arm:
  for moved: Bool
  for b: Bool
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
  ok.edits(Up.edit.toml(moved, Rend.show(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts}),
      Up.edit.if(b, ".gitignore", I.sync(ds, ig), [])),
    I.vended(ds),
    Up.model.next(moved, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ds, ts}, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods,
      ots}),
    ig)

def ok_done.arm(moved, b, _pn, _pe, _pb, _hb, _hbpa, _hbpv, ds, _ts, _ods, _ots, ig):
  match moved b:
    case True{} True{}:
      ({==}, Unit{})
    case True{} False{}:
      ({==}, (+ev => (L1.sync_allowlist_is_the_ledger(ds, ig, ev),
        L1.sync_keeps_other_lines(ds, ig, ev)), Unit{}))
    case False{} True{}:
      Unit{}
    case False{} False{}:
      (+ev => (L1.sync_allowlist_is_the_ledger(ds, ig, ev),
        L1.sync_keeps_other_lines(ds, ig, ev)), Unit{})

law ok_done:
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ig: String
  for fs: List<&2, Up.Found>
  ok.next(Up.done(M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt, ig, fs), ig)

def ok_done(pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, ig, _fs):
  match dd:
    case Up.Deps{+ds, ss, es, dm, dsy, dtr, das, dbad}:
      match tt:
        case Up.Tools{+ts, tm, tsy, tas, tbad}:
          ok_done.arm(Bool.or(dm, tm), String.eq(I.sync(ds, ig), ig), pn, pe, pb, hb, hbpa, hbpv,
            ds, ts, ods, ots, ig)

law ok_srcs:
  for srcs: Up.Srcs
  for +pn: String
  for +pe: String
  for +pb: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for +ods: List<&2, M.Dep>
  for +ots: List<&2, M.Cli>
  for dd: Up.Deps
  for tt: Up.Tools
  for +ig: String
  ok.next(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt, ig), ig)

def ok_srcs(srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, ig):
  match srcs:
    case Up.Srcs{fs}:
      ok_done(pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, ig, fs)
    case Up.SrcsWait{_ask}:
      Unit{}
    case Up.SrcsNo{_why}:
      Unit{}

law ok_ignore:
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
  for +dd: Up.Deps
  for +tt: Up.Tools
  for +rs: List<&2, Up.Reply>
  for es: {Up.text.said(rs, Up.Ignore{}) == said : Up.Said}
  ok.next(Up.got.ignore(said, srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt),
    D2.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_ignore(said, srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, rs, es):
  match said:
    case Up.Said{+x}:
      %Equal.sym(Up.Said, Up.text.said(rs, Up.Ignore{}), Up.Said{x}, es)
        : ok.next(Up.got.srcs(srcs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt, x),
          D2.ignore.said(_))
      ok_srcs(srcs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, x)
    case Up.Unsaid{_why}:
      Unit{}
    case Up.Unasked{_ask}:
      Unit{}

law ok_asks:
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
  for +dd: Up.Deps
  for +tt: Up.Tools
  ok.next(Up.pins.asks(asks, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt),
    D2.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_asks(asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt):
  match asks:
    case []:
      ok_ignore(Up.text.said(rs, Up.Ignore{}),
        Up.ask.srcs(List.is_empty(&2, U.Swap, Up.deps.edits(dd)), rs),
        pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt, rs, {==})
    case _h <> _t:
      Unit{}

law ok_bad:
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
  for +dd: Up.Deps
  for +tt: Up.Tools
  ok.next(Up.pins.bad(clean, bad, asks, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}, dd, tt),
    D2.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_bad(clean, _bad, asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt):
  match clean:
    case True{}:
      ok_asks(asks, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots, dd, tt)
    case False{}:
      Unit{}

law ok_pins:
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
  ok.next(Up.pins(dd, tt, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}),
    D2.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_pins(dd, tt, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots):
  match dd:
    case Up.Deps{+ds, +ss, +es, +dm, +dsy, +dtr, +das, +dbad}:
      match tt:
        case Up.Tools{+ts, +tm, +tsy, +tas, +tbad}:
          ok_bad(Bool.and(String.is_empty(dbad), String.is_empty(tbad)),
            Bool.pick(String, String.is_empty(dbad), tbad, dbad),
            List.append(&2, Up.Ask, das, tas), rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots,
            Up.Deps{ds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{ts, tm, tsy, [], ""})

law ok_known:
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
  ok.next(Up.known(ok, only, rs, M.Manifest{pn, pe, pb, hb, hbpa, hbpv, ods, ots}),
    D2.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_known(ok, only, rs, pn, pe, pb, hb, hbpa, hbpv, ods, ots):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      ok_pins(Up.deps.walk(rs, only, M.hub.or(hb), ods), Up.tools.walk(rs, only, ots), rs,
        pn, pe, pb, hb, hbpa, hbpv, ods, ots)

# LAW: every decision `ez lock --upgrade` makes writes only ez.toml over the
# ledger it renders and `.gitignore` as `I.sync` makes it
law ok_next:
  for +only: String
  for r: M.Read
  for +rs: List<&2, Up.Reply>
  ok.next(Up.next(only, r, rs), D2.ignore.said(Up.text.said(rs, Up.Ignore{})))

def ok_next(only, r, rs):
  match r:
    case M.Bad{_why}:
      Unit{}
    case M.Good{m}:
      match m:
        case M.Manifest{+pn, +pe, +pb, +hb, +hbpa, +hbpv, +ods, +ots}:
          ok_known(Bool.or(U.known(only, ods), M.tool.known(only, ots)), only, rs,
            pn, pe, pb, hb, hbpa, hbpv, ods, ots)

# LAW: and so does every decision `ez lock` makes on a World, plain or not
law ok_world:
  for +args: W.Args
  for +ledger: Maybe<&2, String>
  for +ups: List<&2, Up.Reply>
  ok.next(W.next(args, ledger, ups), D2.ignore.said(Up.text.said(ups, Up.Ignore{})))

def ok_world(args, ledger, ups):
  match args:
    case W.Args{up, +only, +here}:
      match up:
        case False{}:
          Unit{}
        case True{}:
          ok_next(only, W.parsed(ledger), ups)

# The sources. Each is written only when the moves change it.

# LAW: one source, with whether the moves change it given as a parameter:
# written at its own path, or not written
law src_miss.arm:
  for b: Bool
  for +a: String
  for +m: String
  for +es: List<&2, Up.Edit>
  for +rest: List<&2, P.Effect>
  for +p: String
  for ne: {String.eq(a, p) == False{} : Bool}
  {P.put.in(P.edits.of(Up.edit.if(b, a, m, es), rest), p)
    == P.put.in(P.edits.of(es, rest), p) : P.Wrote}

def src_miss.arm(b, a, m, es, rest, p, ne):
  match b:
    case True{}:
      {==}
    case False{}:
      M1.put_one_other(a, m, p, P.put.in(P.edits.of(es, rest), p), ne)

# LAW: sources none of which is at a path leave it as it was
law src_miss:
  for fs: List<&2, Up.Found>
  for +sw: List<&2, U.Swap>
  for +rest: List<&2, P.Effect>
  for +p: String
  for +m: {D2.found.miss(fs, p) == True{} : Bool}
  {P.put.in(P.edits.of(Up.edit.sources(fs, sw), rest), p) == P.put.in(rest, p) : P.Wrote}

def src_miss(fs, sw, rest, p, m):
  match fs:
    case []:
      {==}
    case Up.Found{+a, +x} <> +tl:
      Equal.trans(P.Wrote,
        P.put.in(P.edits.of(Up.edit.if(String.eq(U.reimport.many(sw, x), x), a,
          U.reimport.many(sw, x), Up.edit.sources(tl, sw)), rest), p),
        P.put.in(P.edits.of(Up.edit.sources(tl, sw), rest), p),
        P.put.in(rest, p),
        src_miss.arm(String.eq(U.reimport.many(sw, x), x), a, U.reimport.many(sw, x),
          Up.edit.sources(tl, sw), rest, p,
          Eq.not.true(String.eq(a, p),
            Eq.and.left(Bool.not(String.eq(a, p)), D2.found.miss(tl, p), m))),
        src_miss(tl, sw, rest, p,
          Eq.and.right(Bool.not(String.eq(a, p)), D2.found.miss(tl, p), m)))
