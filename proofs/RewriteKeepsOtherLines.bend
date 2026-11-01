# proofs of laws/RewriteKeepsOtherLines.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/upgrade.bend as U
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../laws/RewriteGoesLineByLine.bend as L1
import ../laws/RewriteKeepsOtherLines.bend as Laws
import ../laws/UpgradeRewritesSources.bend as L2
import ../laws/defs/WorldAfterLock.bend as D1
import ./lemmas/ImportLineRewrite.bend as M1
import ./lemmas/UpgradeSourceWrites.bend as M2
import ./lemmas/UpgradeWritesAroundLedger.bend as M3

def Laws.rewrite_keeps_other_lines(ss, text, i, ok, miss):
  Equal.trans(String,
    D1.line.at(String.lines(U.reimport.many(ss, text)), i),
    D1.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
    D1.line.at(String.lines(text), i),
    Equal.cong(List<&2, String>, String, ls => D1.line.at(ls, i),
      String.lines(U.reimport.many(ss, text)),
      U.reimport.many.lines(ss, String.lines(text)),
      L1.rewrite_by_line(ss, text, ok)),
    Equal.trans(String,
      D1.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
      U.reimport.many.line(ss, D1.line.at(String.lines(text), i)),
      D1.line.at(String.lines(text), i),
      M1.at_many(ss, String.lines(text), i),
      M1.many_keeps(ss, D1.line.at(String.lines(text), i), miss)))

# LAW: rewriting every line keeps their number
law many_length:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  {List.length(&2, String, U.reimport.many.lines(ss, ls))
    == List.length(&2, String, ls) : Nat}

def many_length(ss, ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(Nat, Nat, x => 1n+x,
        List.length(&2, String, U.reimport.many.lines(ss, t)),
        List.length(&2, String, t), many_length(ss, t))

def Laws.rewrite_keeps_line_count(ss, text, ok):
  Equal.trans(Nat,
    List.length(&2, String, String.lines(U.reimport.many(ss, text))),
    List.length(&2, String, U.reimport.many.lines(ss, String.lines(text))),
    List.length(&2, String, String.lines(text)),
    Equal.cong(List<&2, String>, Nat, ls => List.length(&2, String, ls),
      String.lines(U.reimport.many(ss, text)),
      U.reimport.many.lines(ss, String.lines(text)),
      L1.rewrite_by_line(ss, text, ok)),
    many_length(ss, String.lines(text)))

# LAW: lines none of which a move names are left as they are
law many_lines_keep:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  for +none: {Laws.names.none.all(ss, ls) == True{} : Bool}
  {U.reimport.many.lines(ss, ls) == ls : List<&2, String>}

def many_lines_keep(ss, ls, none):
  match ls:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        U.reimport.many.line(ss, h) <> U.reimport.many.lines(ss, t),
        h <> U.reimport.many.lines(ss, t),
        h <> t,
        Equal.cong(String, List<&2, String>, x => x <> U.reimport.many.lines(ss, t),
          U.reimport.many.line(ss, h), h,
          M1.many_keeps(ss, h, Eq.and.left(Laws.names.none(ss, h), Laws.names.none.all(ss, t),
            none))),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          U.reimport.many.lines(ss, t), t,
          many_lines_keep(ss, t, Eq.and.right(Laws.names.none(ss, h),
            Laws.names.none.all(ss, t), none))))

def Laws.rewrite_nothing_named(ss, text, none):
  Equal.trans(String,
    String.join(U.reimport.many.lines(ss, String.split(text, '\n')), "\n"),
    String.join(String.split(text, '\n'), "\n"),
    text,
    Equal.cong(List<&2, String>, String, ls => String.join(ls, "\n"),
      U.reimport.many.lines(ss, String.split(text, '\n')), String.split(text, '\n'),
      many_lines_keep(ss, String.split(text, '\n'), none)),
    Str.join_split(text, '\n'))

def Laws.upgrade_leaves_other_lines(w, at, text, pre, post, fs, mp, mq, bend, ok, i, mv, miss):
  %Equal.sym(String, D1.left.at(P.put(w, at), text), U.reimport.many(D1.swaps(w), text),
    L2.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok))
    : {D1.line.at(String.lines(_), i) == D1.line.at(String.lines(text), i) : String}
  Laws.rewrite_keeps_other_lines(D1.swaps(w), text, i, mv, miss)

def Laws.upgrade_keeps_line_count(w, at, text, pre, post, fs, mp, mq, bend, ok, mv):
  %Equal.sym(String, D1.left.at(P.put(w, at), text), U.reimport.many(D1.swaps(w), text),
    L2.upgrade_rewrites_sources(w, at, text, pre, post, fs, mp, mq, bend, ok))
    : {List.length(&2, String, String.lines(_))
      == List.length(&2, String, String.lines(text)) : Nat}
  Laws.rewrite_keeps_line_count(D1.swaps(w), text, mv)

# LAW: a source the moves leave as it was is not written
law kept_of:
  for +m: String
  for +text: String
  for +e: {m == text : String}
  {M2.wrote.of(String.eq(m, text), m) == P.Kept{} : P.Wrote}

def kept_of(m, text, e):
  %Equal.sym(String, m, text, e) : {M2.wrote.of(String.eq(_, text), _) == P.Kept{} : P.Wrote}
  %Equal.sym(Bool, String.eq(text, text), True{}, Eq.string_eq_self(text))
    : {M2.wrote.of(_, text) == P.Kept{} : P.Wrote}
  {==}

# LAW: a plan leaves a source none of whose lines names a moved hash
# unwritten, whether it is made or refused
law hits_arm:
  for d: P.Doc
  for +nx: Up.Next
  for +cs: List<&2, String>
  for +js: List<&2, W.Judged>
  for +at: String
  for +text: String
  for +pre: List<&2, Up.Found>
  for +post: List<&2, Up.Found>
  for +ig: String
  for okn: M3.ok.next(nx, ig)
  for efs: {Up.next.found(nx) == List.append(&2, Up.Found, pre, Up.Found{at, text} <> post)
    : List<&2, Up.Found>}
  for +mp: {D1.found.miss(pre, at) == True{} : Bool}
  for +mq: {D1.found.miss(post, at) == True{} : Bool}
  for +bend: {String.ends_with(at, ".bend") == True{} : Bool}
  for none: {Laws.names.none.all(Up.next.swaps(nx), String.lines(text)) == True{} : Bool}
  {P.put.plan(P.made(nx, cs, js, d), at) == P.Kept{} : P.Wrote}

def hits_arm(d, nx, cs, js, at, text, pre, post, ig, okn, efs, mp, mq, bend, none):
  match d:
    case P.Stop{_why}:
      {==}
    case P.Doc{+lt}:
      Equal.trans(P.Wrote,
        P.put.plan(P.made(nx, cs, js, P.Doc{lt}), at),
        M2.wrote.of(String.eq(U.reimport.many(Up.next.swaps(nx), text), text),
          U.reimport.many(Up.next.swaps(nx), text)),
        P.Kept{},
        M2.made_src(nx, cs, js, lt, at, text, pre, post, ig, okn, efs, mp, mq, bend),
        kept_of(U.reimport.many(Up.next.swaps(nx), text), text,
          Laws.rewrite_nothing_named(Up.next.swaps(nx), text, none)))

def Laws.upgrade_writes_only_hits(w, at, text, pre, post, fs, mp, mq, bend, none):
  match w:
    case W.World{+args, +ledger, +listing, +replies, +ups}:
      hits_arm(P.decide(W.Inputs{Up.next.read(W.next(args, ledger, ups)),
          Up.next.stop(W.next(args, ledger, ups)),
          W.listing.of(W.next(args, ledger, ups), listing),
          W.judged.of(W.next(args, ledger, ups), replies)}),
        W.next(args, ledger, ups),
        P.cloned(W.replies.of(W.next(args, ledger, ups), replies)),
        W.judged.of(W.next(args, ledger, ups), replies),
        at, text, pre, post, D1.ignore.said(Up.text.said(ups, Up.Ignore{})),
        M3.ok_world(args, ledger, ups), fs, mp, mq, bend, none)
