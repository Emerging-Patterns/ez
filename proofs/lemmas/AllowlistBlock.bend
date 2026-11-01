# the allowlist block names exactly the vendored hashes, put down once
import Base
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/ignore.bend as I
import ../../src/add/world.bend as A
import ../../laws/GitignoreAllowlistIsLedger.bend as L1
import ./NewlineFreeLines.bend as M1

# LAW: a line's hash goes in front whatever follows it
law hashes_put_app:
  for k: I.Rule
  for a: List<&2, String>
  for b: List<&2, String>
  {I.hashes.put(k, List.append(&2, String, a, b))
    == List.append(&2, String, I.hashes.put(k, a), b) : List<&2, String>}

def hashes_put_app(k, _a, _b):
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

# LAW: the allowlist of two runs of lines is the one's then the other's
law hashes_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {I.hashes(List.append(&2, String, xs, ys))
    == List.append(&2, String, I.hashes(xs), I.hashes(ys)) : List<&2, String>}

def hashes_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(List.append(&2, String, t, ys))),
        I.hashes.put(I.kind(h),
          List.append(&2, String, I.hashes(t), I.hashes(ys))),
        List.append(&2, String, I.hashes.put(I.kind(h), I.hashes(t)),
          I.hashes(ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          y => I.hashes.put(I.kind(h), y),
          I.hashes(List.append(&2, String, t, ys)),
          List.append(&2, String, I.hashes(t), I.hashes(ys)),
          hashes_app(t, ys)),
        hashes_put_app(I.kind(h), I.hashes(t), I.hashes(ys)))

# LAW: the lines ez writes for hashes that name something name exactly those
# hashes, in order
law hashes_each:
  for +hs: List<&2, String>
  for +e: {M1.full.all(hs) == True{} : Bool}
  {I.hashes(I.allow.each(hs)) == hs : List<&2, String>}

def hashes_each(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(I.allow(h)), I.hashes(I.allow.each(t))),
        I.hashes.put(I.Allow{h}, I.hashes(I.allow.each(t))),
        h <> t,
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.allow.each(t))),
          I.kind(I.allow(h)), I.Allow{h}, M1.kind_allow(h, M1.full_head(h, t, e))),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.hashes(I.allow.each(t)), t, hashes_each(t, M1.full_tail(h, t, e))))

# LAW: the three rules name no hash, whichever of them are written
law rules_name_no_hash:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {I.hashes(I.rules.go(b1, b2, b3)) == [] : List<&2, String>}

def rules_name_no_hash(b1, b2, b3):
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

# LAW: the rules, written or not, name no hash
law need_hashes:
  for s: Bool
  for +rs: List<&2, String>
  for h: {I.hashes(rs) == [] : List<&2, String>}
  {I.hashes(I.need(s, rs)) == [] : List<&2, String>}

def need_hashes(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: the block names exactly the vendored hashes
law block_hashes:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, I.Line>
  {I.hashes(I.block(ds, ls)) == I.vended(ds) : List<&2, String>}

def block_hashes(ds, ls):
  Equal.trans(List<&2, String>,
    I.hashes(List.append(&2, String,
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds))),
    List.append(&2, String,
      I.hashes(I.need(Bool.or(I.has(ls, I.Dir{}),
        List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
      I.hashes(I.allows(ds))),
    I.vended(ds),
    hashes_app(
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds)),
    Equal.trans(List<&2, String>,
      List.append(&2, String,
        I.hashes(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        I.hashes(I.allows(ds))),
      I.hashes(I.allows(ds)),
      I.vended(ds),
      Equal.cong(List<&2, String>, List<&2, String>,
        y => List.append(&2, String, y, I.hashes(I.allows(ds))),
        I.hashes(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        [],
        need_hashes(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls),
          rules_name_no_hash(I.has(ls, I.Star{}), I.has(ls, I.Lib{}),
            I.has(ls, I.Pkgs{})))),
      hashes_each(I.vended(ds), M1.vended_full(ds))))

# LAW: the block, put down or not, names what it holds or nothing
law hashes_placed:
  for +d: Bool
  for +blk: List<&2, String>
  {I.hashes(I.placed(d, blk)) == I.placed(d, I.hashes(blk)) : List<&2, String>}

def hashes_placed(d, _blk):
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: one line of the walk, with its kind given as a parameter. A line of
# the project's or one of the three rules is kept and names no hash, a
# `.ez/` gives way to rules that name none, and the first allowlist line
# gives way to the block, which the rest of the walk does not put down again.
law walk_hashes.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +hf: {I.hashes(fix) == [] : List<&2, String>}
  for ihd: {I.hashes(I.walk(I.tag(t), fix, blk, d)) == I.placed(d, I.hashes(blk))
    : List<&2, String>}
  for iht: {I.hashes(I.walk(I.tag(t), fix, blk, True{})) == []
    : List<&2, String>}
  {I.hashes(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d))
    == I.placed(d, I.hashes(blk)) : List<&2, String>}

def walk_hashes.arm(k, h, t, fix, blk, d, ek, hf, ihd, iht):
  match k:
    case I.Other{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Other{}, ek),
        ihd)
    case I.Star{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Star{}, ek),
        ihd)
    case I.Lib{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Lib{}, ek),
        ihd)
    case I.Pkgs{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Pkgs{}, ek),
        ihd)
    case I.Dir{}:
      Equal.trans(List<&2, String>,
        I.hashes(List.append(&2, String, fix, I.walk(I.tag(t), fix, blk, d))),
        List.append(&2, String, I.hashes(fix),
          I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.placed(d, I.hashes(blk)),
        hashes_app(fix, I.walk(I.tag(t), fix, blk, d)),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.hashes(fix),
            I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.hashes(I.walk(I.tag(t), fix, blk, d)),
          I.placed(d, I.hashes(blk)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, y,
              I.hashes(I.walk(I.tag(t), fix, blk, d))),
            I.hashes(fix), [], hf),
          ihd))
    case I.Allow{x}:
      Equal.trans(List<&2, String>,
        I.hashes(List.append(&2, String, I.placed(d, blk),
          I.walk(I.tag(t), fix, blk, True{}))),
        List.append(&2, String, I.hashes(I.placed(d, blk)),
          I.hashes(I.walk(I.tag(t), fix, blk, True{}))),
        I.placed(d, I.hashes(blk)),
        hashes_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{})),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.hashes(I.placed(d, blk)),
            I.hashes(I.walk(I.tag(t), fix, blk, True{}))),
          List.append(&2, String, I.hashes(I.placed(d, blk)), []),
          I.placed(d, I.hashes(blk)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, I.hashes(I.placed(d, blk)), y),
            I.hashes(I.walk(I.tag(t), fix, blk, True{})), [], iht),
          Equal.trans(List<&2, String>,
            List.append(&2, String, I.hashes(I.placed(d, blk)), []),
            I.hashes(I.placed(d, blk)),
            I.placed(d, I.hashes(blk)),
            M1.lines_app_nil(I.hashes(I.placed(d, blk))),
            hashes_placed(d, blk))))

# LAW: the walk's allowlist is the block, once, or nothing when the block is
# already down
law walk_hashes:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +hf: {I.hashes(fix) == [] : List<&2, String>}
  {I.hashes(I.walk(I.tag(raw), fix, blk, d)) == I.placed(d, I.hashes(blk))
    : List<&2, String>}

def walk_hashes(raw, fix, blk, d, hf):
  match raw:
    case []:
      hashes_placed(d, blk)
    case +h <> +t:
      walk_hashes.arm(I.kind(h), h, t, fix, blk, d, {==}, hf,
        walk_hashes(t, fix, blk, d, hf), walk_hashes(t, fix, blk, True{}, hf))

# The walk puts the block down once, and the block is the ledger's hashes.
def L1.allowlist_is_the_ledger(ds, ls):
  Equal.trans(List<&2, String>,
    I.hashes(I.walk(I.tag(ls), I.rules(I.tag(ls)), I.block(ds, I.tag(ls)),
      False{})),
    I.hashes(I.block(ds, I.tag(ls))),
    I.vended(ds),
    walk_hashes(ls, I.rules(I.tag(ls)), I.block(ds, I.tag(ls)), False{},
      rules_name_no_hash(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))),
    block_hashes(ds, I.tag(ls)))

# LAW: the file `sync` writes, with whether its lines changed given as a
# parameter, reads back as the lines `I.lines` made from the file it read.
# Unchanged lines leave the file as it was, whose lines were those already.
law sync_lines.arm:
  for +ds: List<&2, M.Dep>
  for +text: String
  for b: Bool
  for eb: {String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
    I.file.text(I.file.lines(text))) == b : Bool}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.file.lines(I.text.out(b, text, I.file.text(I.lines(ds, I.file.lines(text)))))
    == I.lines(ds, I.file.lines(text)) : List<&2, String>}

def sync_lines.arm(ds, text, b, eb, ev):
  match b:
    case True{}:
      Equal.sym(List<&2, String>, I.lines(ds, I.file.lines(text)), I.file.lines(text),
        Equal.trans(List<&2, String>,
          I.lines(ds, I.file.lines(text)),
          I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
          I.file.lines(text),
          Equal.sym(List<&2, String>,
            I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
            I.lines(ds, I.file.lines(text)),
            M1.file_lines_text(I.lines(ds, I.file.lines(text)),
              M1.lines_clear(ds, I.file.lines(text), M1.file_lines_clear(text), ev))),
          Equal.trans(List<&2, String>,
            I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
            I.file.lines(I.file.text(I.file.lines(text))),
            I.file.lines(text),
            Equal.cong(String, List<&2, String>, x => I.file.lines(x),
              I.file.text(I.lines(ds, I.file.lines(text))),
              I.file.text(I.file.lines(text)),
              Str.string_eq_true(I.file.text(I.lines(ds, I.file.lines(text))),
                I.file.text(I.file.lines(text)), eb)),
            M1.file_lines_text(I.file.lines(text), M1.file_lines_clear(text)))))
    case False{}:
      M1.file_lines_text(I.lines(ds, I.file.lines(text)),
        M1.lines_clear(ds, I.file.lines(text), M1.file_lines_clear(text), ev))

# LAW: the file `sync` writes reads back as the lines `I.lines` made from the
# file it read, whatever that file ended with
law sync_lines:
  for +ds: List<&2, M.Dep>
  for +text: String
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.file.lines(I.sync(ds, text)) == I.lines(ds, I.file.lines(text))
    : List<&2, String>}

def sync_lines(ds, text, ev):
  sync_lines.arm(ds, text,
    String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
      I.file.text(I.file.lines(text))), {==}, ev)

# The file's lines are what `I.lines` made, so the line laws hold of it.
def L1.sync_allowlist_is_the_ledger(ds, text, ev):
  Equal.trans(List<&2, String>,
    I.hashes(I.file.lines(I.sync(ds, text))),
    I.hashes(I.lines(ds, I.file.lines(text))),
    I.vended(ds),
    Equal.cong(List<&2, String>, List<&2, String>, y => I.hashes(y),
      I.file.lines(I.sync(ds, text)), I.lines(ds, I.file.lines(text)),
      sync_lines(ds, text, ev)),
    L1.allowlist_is_the_ledger(ds, I.file.lines(text)))

# LAW: a write to another path leaves a path as it was
law put_one_other:
  for +a: String
  for +t: String
  for +p: String
  for r: P.Wrote
  for ne: {String.eq(a, p) == False{} : Bool}
  {P.put.one(P.Write{a, t}, p, r) == r : P.Wrote}

def put_one_other(a, t, p, r, ne):
  match r:
    case P.Kept{}:
      %Equal.sym(Bool, String.eq(a, p), False{}, ne)
        : {Bool.pick(P.Wrote, _, P.Put{t}, P.Kept{}) == P.Kept{} : P.Wrote}
      {==}
    case P.Put{x}:
      {==}
