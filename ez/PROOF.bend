# ez: the proofs. `bend PROOF.bend` is the gate.
#
# The quantified half is a hypothesis rewritten into the one `Bool.pick` or
# `Bool.and` the code branches on, or a prefix test that `starts_append`
# already holds. The rest is a closed computation: both sides are a known
# string or list, so they reduce to the same value and the proof is the
# computation itself.
import Base
import ./drift.bend as D
import ./gate.bend as G
import ./pin.bend as Pin
import ./target.bend as Tgt
import ./named.bend as Named
import ../manifest/manifest.bend as M
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

def Laws.nag_needs_prefix(s, e):
  %e : {Bool.and(_, String.ends_with(s, " is available: run bend update"))
    == False{} : Bool}
  {==}

def Laws.report_opens(rest):
  Equal.cong(Bool, Bool,
    x => Bool.or(x, Bool.and(False{},
      String.starts_with(String.append("All terms check", rest), "- "))),
    String.starts_with(String.append("All terms check", rest), "All terms check"),
    True{},
    Eq.starts_append("All terms check", rest))

def Laws.dash_follows_report(rest):
  Equal.cong(Bool, Bool,
    x => Bool.or(String.starts_with(String.append("- ", rest), "All terms check"),
      Bool.and(True{}, x)),
    String.starts_with(String.append("- ", rest), "- "),
    True{},
    Eq.starts_append("- ", rest))

def Laws.dash_alone_is_output(_rest):
  {==}

def Laws.want_skips(h, t, e):
  %e : {G.want.put(_, h, G.want(t)) == G.want(t) : List<&2, String>}
  {==}

# LAW: nothing taken off the front of a string leaves the string
law drop_zero:
  for +s: String
  {String.drop(s, 0n) == s : String}

def drop_zero(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# LAW: `#|` dropped off a string it was put on leaves the string
law drop_hash_bar:
  for +rest: String
  {String.drop("#|" ++ rest, 2n) == rest : String}

def drop_hash_bar(rest):
  drop_zero(rest)

def Laws.want_keeps(rest, t):
  Equal.trans(List<&2, String>,
    G.want.put(String.starts_with(String.append("#|", rest), "#|"),
      String.append("#|", rest), G.want(t)),
    G.want.put(True{}, String.append("#|", rest), G.want(t)),
    rest <> G.want(t),
    Equal.cong(Bool, List<&2, String>,
      x => G.want.put(x, String.append("#|", rest), G.want(t)),
      String.starts_with(String.append("#|", rest), "#|"), True{},
      Eq.starts_append("#|", rest)),
    Equal.cong(String, List<&2, String>, x => x <> G.want(t),
      String.drop(String.append("#|", rest), 2n), rest,
      drop_hash_bar(rest)))

def Laws.hash_of_local(s, e):
  %e : {Bool.pick(String, _,
    D.head(String.split(String.drop(s, 7n), '/')), "") == "" : String}
  {==}

def Laws.hash_of_import():
  {==}

def Laws.hash_of_relative():
  {==}

def Laws.imported_dedups():
  {==}

def Laws.report_agrees():
  {==}

def Laws.report_both_ways():
  {==}

def Laws.report_unused():
  {==}

# The clock's pure half: a non-empty deadline is rewritten into the
# pick that keeps it.

def Laws.by_effect_keeps(d, e):
  %e : {Bool.pick(String, _, "0", d) == d : String}
  {==}

# The command line as parse sees it. Each side is a known list, so the
# proof is the computation itself.

def Laws.argv_of_run():
  {==}

def Laws.argv_of_tool():
  {==}

def Laws.tool_rest_dashes():
  {==}

def Laws.tool_rest_plain():
  {==}

# target: each law's word is built from literal chars around the parts that
# are left open, so the chars that decide it compute. What does not compute is
# a fact about an open part, and each of those is a lemma below.

# LAW: a word with a char in front of anything is not empty
law nonempty_app:
  for a: String
  for c: Char
  for t: String
  {False{} == String.is_empty(a ++ SCon{c, t}) : Bool}

def nonempty_app(a, _c, _t):
  match a:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

# LAW: one char of a search for `://`, with whether the pattern starts there
# given as a parameter
law contains_url.arm:
  for +t: String
  for s: Bool
  for ih: {String.contains(t, "://") == True{} : Bool}
  {String.contains.if(t, "://", s) == True{} : Bool}

def contains_url.arm(_t, s, ih):
  match s:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: `://` is found wherever it is put
law contains_url:
  for +a: String
  for +b: String
  {String.contains(a ++ ("://" ++ b), "://") == True{} : Bool}

def contains_url(a, b):
  match a:
    case SNil{}:
      %Equal.sym(Bool, String.starts_with(b, ""), True{}, Eq.starts_nil(b)) :
        {String.contains.if("//" ++ b, "://", _) == True{} : Bool}
      {==}
    case SCon{+h, +t}:
      contains_url.arm(t ++ ("://" ++ b),
        String.starts_with(SCon{h, t ++ ("://" ++ b)}, "://"),
        contains_url(t, b))

# LAW: a word that reached the URL arm with `://` in it is a URL
law url_of:
  for +text: String
  for ne: {False{} == String.is_empty(text) : Bool}
  for c: {True{} == String.contains(text, "://") : Bool}
  {Tgt.classify(text) == Tgt.remote(text, Tgt.slug.url(text)) : Tgt.Place}

def url_of(text, ne, c):
  %ne : {Tgt.classify.empty(_, text) == Tgt.remote(text, Tgt.slug.url(text))
    : Tgt.Place}
  %c : {Tgt.classify.url(_, text) == Tgt.remote(text, Tgt.slug.url(text))
    : Tgt.Place}
  {==}

def Laws.classify_url(a, b):
  url_of(a ++ ("://" ++ b), nonempty_app(a, ':', "//" ++ b),
    Equal.sym(Bool, String.contains(a ++ ("://" ++ b), "://"), True{},
      contains_url(a, b)))

# The prefix laws: the premise rules out `://`, and the literal chars of the
# prefix decide the rest.

def Laws.classify_scp(rest, e):
  %e : {Tgt.classify.url(_, "git@" ++ rest)
    == Tgt.remote("git@" ++ rest, Tgt.slug.scp("git@" ++ rest)) : Tgt.Place}
  %Equal.sym(Bool, String.starts_with(rest, ""), True{}, Eq.starts_nil(rest)) :
    {Tgt.classify.scp(_, "git@" ++ rest)
      == Tgt.remote("git@" ++ rest, Tgt.slug.scp("git@" ++ rest)) : Tgt.Place}
  {==}

def Laws.classify_abs(rest, e):
  %e : {Tgt.classify.url(_, "/" ++ rest) == Tgt.Local{"/" ++ rest} : Tgt.Place}
  {==}

def Laws.classify_here(rest, e):
  %e : {Tgt.classify.url(_, "./" ++ rest) == Tgt.Local{"./" ++ rest}
    : Tgt.Place}
  {==}

def Laws.classify_up(rest, e):
  %e : {Tgt.classify.url(_, "../" ++ rest) == Tgt.Local{"../" ++ rest}
    : Tgt.Place}
  {==}

def Laws.classify_home(rest, e):
  %e : {Tgt.classify.url(_, "~/" ++ rest) == Tgt.Local{"~/" ++ rest}
    : Tgt.Place}
  {==}

# The shorthand law. A segment's chars are open, so what is known of each is
# its kind, and the kind is a chain of five tests with the colon asked first.
# Each lemma below lifts a kind, or one test of the chain, into a parameter,
# and closes the arms the premise rules out.

# LAW: a name char that passes lets the rest of the name be asked about
law keep_true:
  for k: Tgt.Mark
  for +t: String
  for e: {Tgt.name.keep(k, _u => Tgt.name.all(t)) == True{} : Bool}
  {Tgt.name.all(t) == True{} : Bool}

def keep_true(k, t, e):
  match k:
    case Tgt.Word{}:
      e
    case Tgt.Dot{}:
      e
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.name.all(t) == True{} : Bool}, e)
    case Tgt.Tilde{}:
      Eq.bit.absurd(&2, {Tgt.name.all(t) == True{} : Bool}, e)
    case Tgt.Other{}:
      Eq.bit.absurd(&2, {Tgt.name.all(t) == True{} : Bool}, e)

# LAW: one char of a name is not a colon, so `://` does not start there
law no_url.arm:
  for +r: String
  for +t: String
  for c: Bool
  for s: Bool
  for d: Bool
  for ti: Bool
  for w: Bool
  for e: {Tgt.name.keep(Tgt.kind.colon(c, s, d, ti, w), _u => Tgt.name.all(r))
    == True{} : Bool}
  for ih: {Tgt.name.all(r) == True{} : Bool}
    -> {String.contains(r ++ t, "://") == String.contains(t, "://") : Bool}
  {String.contains.if(r ++ t, "://", String.starts_with.if(r ++ t, "//", c))
    == String.contains(t, "://") : Bool}

def no_url.arm(r, t, c, s, d, ti, w, e, ih):
  match c:
    case True{}:
      Eq.bit.absurd(&2,
        {String.contains.if(r ++ t, "://", String.starts_with.if(r ++ t, "//", True{}))
          == String.contains(t, "://") : Bool}, e)
    case False{}:
      ih(keep_true(Tgt.kind.slash(s, d, ti, w), r, e))

# LAW: a name puts no `://` in front of what follows it
law no_url:
  for +a: String
  for +t: String
  for e: {Tgt.name.all(a) == True{} : Bool}
  {String.contains(a ++ t, "://") == String.contains(t, "://") : Bool}

def no_url(a, t, e):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      no_url.arm(r, t, Char.is_eq(h, ':'), Char.is_eq(h, '/'),
        Char.is_eq(h, '.'), Char.is_eq(h, '~'), Tgt.plain.at(h), e,
        x => no_url(r, t, x))

# LAW: after a leading dot and another, a segment is a name
law seg_name.dots:
  for +t: String
  for e: {Tgt.seg.dots(t) == True{} : Bool}
  {Tgt.name.all(t) == True{} : Bool}

def seg_name.dots(t, e):
  match t:
    case SNil{}:
      Eq.bit.absurd(&2, {Tgt.name.all(SNil{}) == True{} : Bool}, e)
    case SCon{_h, _r}:
      e

# LAW: after a leading dot, a segment's second char and on are a name
law seg_name.dot2:
  for k: Tgt.Mark
  for +t: String
  for e: {Tgt.seg.dot2(k, t) == True{} : Bool}
  {Tgt.name.keep(k, _u => Tgt.name.all(t)) == True{} : Bool}

def seg_name.dot2(k, t, e):
  match k:
    case Tgt.Word{}:
      e
    case Tgt.Dot{}:
      seg_name.dots(t, e)
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.name.keep(Tgt.Slash{}, _u => Tgt.name.all(t))
        == True{} : Bool}, e)
    case Tgt.Tilde{}:
      Eq.bit.absurd(&2, {Tgt.name.keep(Tgt.Tilde{}, _u => Tgt.name.all(t))
        == True{} : Bool}, e)
    case Tgt.Other{}:
      Eq.bit.absurd(&2, {Tgt.name.keep(Tgt.Other{}, _u => Tgt.name.all(t))
        == True{} : Bool}, e)

# LAW: after a leading dot, the rest of a segment is a name
law seg_name.dot:
  for +t: String
  for e: {Tgt.seg.dot(t) == True{} : Bool}
  {Tgt.name.all(t) == True{} : Bool}

def seg_name.dot(t, e):
  match t:
    case SNil{}:
      Eq.bit.absurd(&2, {Tgt.name.all(SNil{}) == True{} : Bool}, e)
    case SCon{+h, +r}:
      seg_name.dot2(Tgt.kind(h), r, e)

# LAW: a segment's first char and on are a name
law seg_name.first:
  for k: Tgt.Mark
  for +t: String
  for e: {Tgt.seg.first(k, t) == True{} : Bool}
  {Tgt.name.keep(k, _u => Tgt.name.all(t)) == True{} : Bool}

def seg_name.first(k, t, e):
  match k:
    case Tgt.Word{}:
      e
    case Tgt.Dot{}:
      seg_name.dot(t, e)
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.name.keep(Tgt.Slash{}, _u => Tgt.name.all(t))
        == True{} : Bool}, e)
    case Tgt.Tilde{}:
      Eq.bit.absurd(&2, {Tgt.name.keep(Tgt.Tilde{}, _u => Tgt.name.all(t))
        == True{} : Bool}, e)
    case Tgt.Other{}:
      Eq.bit.absurd(&2, {Tgt.name.keep(Tgt.Other{}, _u => Tgt.name.all(t))
        == True{} : Bool}, e)

# LAW: a segment is a name
law seg_name:
  for +a: String
  for e: {Tgt.seg(a) == True{} : Bool}
  {Tgt.name.all(a) == True{} : Bool}

def seg_name(a, e):
  match a:
    case SNil{}:
      Eq.bit.absurd(&2, {Tgt.name.all(SNil{}) == True{} : Bool}, e)
    case SCon{+h, +t}:
      seg_name.first(Tgt.kind(h), t, e)

# LAW: one char of a name is carried onto the left half
law halve_name.arm:
  for k: Tgt.Mark
  for +h: Char
  for +t: String
  for +b: String
  for e: {Tgt.name.keep(k, _u => Tgt.name.all(t)) == True{} : Bool}
  for ih: {Tgt.name.all(t) == True{} : Bool}
    -> {Tgt.halve(t ++ ("/" ++ b)) == Tgt.Two{t, b} : Tgt.Halves}
  {Tgt.halve.at(k, h, t ++ ("/" ++ b), _u => Tgt.halve(t ++ ("/" ++ b)))
    == Tgt.Two{SCon{h, t}, b} : Tgt.Halves}

def halve_name.arm(k, h, t, b, e, ih):
  match k:
    case Tgt.Word{}:
      Equal.cong(Tgt.Halves, Tgt.Halves, y => Tgt.halve.put(h, y),
        Tgt.halve(t ++ ("/" ++ b)), Tgt.Two{t, b}, ih(e))
    case Tgt.Dot{}:
      Equal.cong(Tgt.Halves, Tgt.Halves, y => Tgt.halve.put(h, y),
        Tgt.halve(t ++ ("/" ++ b)), Tgt.Two{t, b}, ih(e))
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.Two{"", t ++ ("/" ++ b)} == Tgt.Two{SCon{h, t}, b}
        : Tgt.Halves}, e)
    case Tgt.Tilde{}:
      Eq.bit.absurd(&2, {Tgt.Uncut{} == Tgt.Two{SCon{h, t}, b} : Tgt.Halves}, e)
    case Tgt.Other{}:
      Eq.bit.absurd(&2, {Tgt.Uncut{} == Tgt.Two{SCon{h, t}, b} : Tgt.Halves}, e)

# LAW: a name and what follows its slash are the two halves
law halve_name:
  for +a: String
  for +b: String
  for e: {Tgt.name.all(a) == True{} : Bool}
  {Tgt.halve(a ++ ("/" ++ b)) == Tgt.Two{a, b} : Tgt.Halves}

def halve_name(a, b, e):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      halve_name.arm(Tgt.kind(h), h, t, b, e, x => halve_name(t, b, x))

# LAW: a char that ends a name is not a slash
law looks_slash:
  for k: Tgt.Mark
  for +t: String
  for e: {Tgt.name.keep(k, _u => Tgt.name.all(t)) == True{} : Bool}
  {Tgt.looks.slash.at(k) == False{} : Bool}

def looks_slash(k, _t, e):
  match k:
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.looks.slash.at(Tgt.Slash{}) == False{} : Bool}, e)
    case Tgt.Dot{}:
      {==}
    case Tgt.Tilde{}:
      {==}
    case Tgt.Word{}:
      {==}
    case Tgt.Other{}:
      {==}

# LAW: after `..`, a segment is not followed by a slash
law looks_dots:
  for +t: String
  for +x: String
  for e: {Tgt.seg.dots(t) == True{} : Bool}
  {Tgt.looks.slash(t ++ x) == False{} : Bool}

def looks_dots(t, x, e):
  match t:
    case SNil{}:
      Eq.bit.absurd(&2, {Tgt.looks.slash(x) == False{} : Bool}, e)
    case SCon{+h, +r}:
      looks_slash(Tgt.kind(h), r, e)

# LAW: after a leading dot, a segment's second char does not make `./`
# or `../`
law looks_dot2:
  for k: Tgt.Mark
  for +t: String
  for +x: String
  for e: {Tgt.seg.dot2(k, t) == True{} : Bool}
  {Tgt.looks.dot.at(k, t ++ x) == False{} : Bool}

def looks_dot2(k, t, x, e):
  match k:
    case Tgt.Word{}:
      {==}
    case Tgt.Dot{}:
      looks_dots(t, x, e)
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.looks.dot.at(Tgt.Slash{}, t ++ x) == False{} : Bool}, e)
    case Tgt.Tilde{}:
      {==}
    case Tgt.Other{}:
      {==}

# LAW: a segment that starts with a dot does not start `./` or `../`
law looks_dot:
  for +t: String
  for +x: String
  for e: {Tgt.seg.dot(t) == True{} : Bool}
  {Tgt.looks.dot(t ++ x) == False{} : Bool}

def looks_dot(t, x, e):
  match t:
    case SNil{}:
      Eq.bit.absurd(&2, {Tgt.looks.dot(x) == False{} : Bool}, e)
    case SCon{+h, +r}:
      looks_dot2(Tgt.kind(h), r, x, e)

# LAW: a segment's first char does not start a path
law looks_first:
  for k: Tgt.Mark
  for +t: String
  for +x: String
  for e: {Tgt.seg.first(k, t) == True{} : Bool}
  {Tgt.looks.first(k, t ++ x) == False{} : Bool}

def looks_first(k, t, x, e):
  match k:
    case Tgt.Word{}:
      {==}
    case Tgt.Dot{}:
      looks_dot(t, x, e)
    case Tgt.Slash{}:
      Eq.bit.absurd(&2, {Tgt.looks.first(Tgt.Slash{}, t ++ x) == False{} : Bool}, e)
    case Tgt.Tilde{}:
      Eq.bit.absurd(&2, {Tgt.looks.first(Tgt.Tilde{}, t ++ x) == False{} : Bool}, e)
    case Tgt.Other{}:
      {==}

# LAW: a word that starts with a segment does not look like a path, since
# a segment is neither `.` nor `..` and holds no `/` or `~`
law looks_seg:
  for +a: String
  for +x: String
  for e: {Tgt.seg(a) == True{} : Bool}
  {Tgt.looks.path(a ++ x) == False{} : Bool}

def looks_seg(a, x, e):
  match a:
    case SNil{}:
      Eq.bit.absurd(&2, {Tgt.looks.path(x) == False{} : Bool}, e)
    case SCon{+h, +t}:
      looks_first(Tgt.kind(h), t, x, e)

# LAW: three tests that answered as a shorthand needs them to
law and_repo:
  for x: Bool
  for y: Bool
  for z: Bool
  for ex: {x == True{} : Bool}
  for ey: {y == True{} : Bool}
  for ez: {z == False{} : Bool}
  {Bool.and(x, Bool.and(y, Bool.not(z))) == True{} : Bool}

def and_repo(x, y, z, ex, ey, ez):
  %Equal.sym(Bool, x, True{}, ex) :
    {Bool.and(_, Bool.and(y, Bool.not(z))) == True{} : Bool}
  %Equal.sym(Bool, y, True{}, ey) : {Bool.and(_, Bool.not(z)) == True{} : Bool}
  %Equal.sym(Bool, z, False{}, ez) : {Bool.not(_) == True{} : Bool}
  {==}

# LAW: two segments around a slash, the second not a Bend file, are a
# shorthand
law github_two:
  for +a: String
  for +b: String
  for ea: {Tgt.seg(a) == True{} : Bool}
  for eb: {Tgt.seg(b) == True{} : Bool}
  for ef: {Tgt.bend.file(b) == False{} : Bool}
  {Tgt.github.ok(a ++ ("/" ++ b)) == True{} : Bool}

def github_two(a, b, ea, eb, ef):
  +ga = ea
  Equal.trans(Bool,
    Tgt.github.halves(Tgt.halve(a ++ ("/" ++ b))),
    Tgt.github.halves(Tgt.Two{a, b}),
    True{},
    Equal.cong(Tgt.Halves, Bool, y => Tgt.github.halves(y),
      Tgt.halve(a ++ ("/" ++ b)), Tgt.Two{a, b},
      halve_name(a, b, seg_name(a, ga))),
    and_repo(Tgt.seg(a), Tgt.seg(b), Tgt.bend.file(b), ga, eb, ef))

# LAW: nor does the second segment of a shorthand hold `://`
law no_url_two:
  for +a: String
  for +b: String
  for ea: {Tgt.seg(a) == True{} : Bool}
  for eb: {Tgt.seg(b) == True{} : Bool}
  {String.contains(a ++ ("/" ++ b), "://") == False{} : Bool}

def no_url_two(a, b, ea, eb):
  Equal.trans(Bool,
    String.contains(a ++ ("/" ++ b), "://"),
    String.contains(b ++ "", "://"),
    False{},
    Equal.trans(Bool,
      String.contains(a ++ ("/" ++ b), "://"),
      String.contains(b, "://"),
      String.contains(b ++ "", "://"),
      no_url(a, "/" ++ b, seg_name(a, ea)),
      Equal.cong(String, Bool, y => String.contains(y, "://"), b, b ++ "",
        Equal.sym(String, b ++ "", b, Eq.append_nil(b)))),
    no_url(b, "", seg_name(b, eb)))

def Laws.classify_github(a, b, ea, eb, ef):
  +ga = ea
  +gb = eb
  %nonempty_app(a, '/', b) : {Tgt.classify.empty(_, a ++ ("/" ++ b))
    == Tgt.Remote{"https://github.com/" ++ (a ++ ("/" ++ b)),
      "github.com/" ++ Tgt.ungit(a ++ ("/" ++ b))} : Tgt.Place}
  %Equal.sym(Bool, String.contains(a ++ ("/" ++ b), "://"), False{},
    no_url_two(a, b, ga, gb)) : {Tgt.classify.url(_, a ++ ("/" ++ b))
    == Tgt.Remote{"https://github.com/" ++ (a ++ ("/" ++ b)),
      "github.com/" ++ Tgt.ungit(a ++ ("/" ++ b))} : Tgt.Place}
  %Equal.sym(Bool, Tgt.looks.path(a ++ ("/" ++ b)), False{},
    looks_seg(a, "/" ++ b, ga)) : {Tgt.classify.path(_, a ++ ("/" ++ b))
    == Tgt.Remote{"https://github.com/" ++ (a ++ ("/" ++ b)),
      "github.com/" ++ Tgt.ungit(a ++ ("/" ++ b))} : Tgt.Place}
  %Equal.sym(Bool, Tgt.github.ok(a ++ ("/" ++ b)), True{},
    github_two(a, b, ga, gb, ef)) : {Tgt.classify.hub(_, a ++ ("/" ++ b))
    == Tgt.Remote{"https://github.com/" ++ (a ++ ("/" ++ b)),
      "github.com/" ++ Tgt.ungit(a ++ ("/" ++ b))} : Tgt.Place}
  {==}

# The fall-through. A word the premises rule out of every other arm is a
# path, which needs the two tests the classifier reads by kind — whether a
# word looks like a path, and whether it is a shorthand — to answer no
# whenever the plain statement of each does. The first is a fact about the
# char tests alone. The second needs the slash a word was cut at to be `/`,
# which is a fact about `Char.is_eq` that Base does not state: equal code
# words are equal, down to their bits.

# LAW: a comparison that says equal is `EQ`
law cmp_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def cmp_eq(c, e):
  match c:
    case LT{}:
      Eq.bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
    case EQ{}:
      {==}
    case GT{}:
      Eq.bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)

# LAW: two bits that compare equal are the same bit
law bool_eq:
  for a: Bool
  for b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

def bool_eq(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool},
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), LT{}, EQ{}, e))
    case True{} False{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), GT{}, EQ{}, e))
    case True{} True{}:
      {==}

# LAW: one bit of a word comparison, with the tail's answer given as a
# parameter
law word_eq.arm:
  for +p: Nat
  for +ab: Bool
  for +at: Word(p)
  for +bb: Bool
  for +bt: Word(p)
  for t: Cmp
  for et: {Word.cmp(p, at, bt) == t : Cmp}
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  for ih: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)}
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}

def word_eq.arm(p, ab, at, bb, bt, t, et, e, ih):
  match t:
    case LT{}:
      Eq.bit.absurd(&2, {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)},
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), LT{}, EQ{}, e))
    case GT{}:
      Eq.bit.absurd(&2, {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)},
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), GT{}, EQ{}, e))
    case EQ{}:
      +hb = bool_eq(ab, bb, e)
      +tl = ih(et)
      %hb : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
      %tl : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
      {==}

# LAW: two words that compare equal are the same word
law word_eq:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          word_eq.arm(p, ab, at, bb, bt, Word.cmp(p, at, bt), {==}, e,
            x => word_eq(p, at, bt, x))

# LAW: two chars `Char.is_eq` calls equal are the same char
law char_eq:
  for +a: Char
  for +b: Char
  for e: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

def char_eq(a, b, e):
  match a b:
    case Chr{U32{+v}} Chr{U32{+w}}:
      Equal.cong(Word(32n), Char, z => Chr{U32{z}}, v, w,
        word_eq(32n, v, w, cmp_eq(Word.cmp(32n, v, w), e)))

# which half a cut word is, read off it
def two.is(hv: Tgt.Halves) -> Bool:
  match hv:
    case Tgt.Uncut{}:
      False{}
    case Tgt.Two{_l, _r}:
      True{}

def two.left(hv: Tgt.Halves) -> String:
  match hv:
    case Tgt.Uncut{}:
      ""
    case Tgt.Two{l, _r}:
      l

def two.right(hv: Tgt.Halves) -> String:
  match hv:
    case Tgt.Uncut{}:
      ""
    case Tgt.Two{_l, r}:
      r

# LAW: a word that was not cut is not two halves
law uncut_two:
  for -a: String
  for -b: String
  for e: {Tgt.Uncut{} == Tgt.Two{a, b} : Tgt.Halves}
  Empty

def uncut_two(a, b, e):
  Eq.bit.clash(Equal.cong(Tgt.Halves, Bool, x => two.is(x), Tgt.Uncut{},
    Tgt.Two{a, b}, e))

# LAW: a name char carried onto the left half of the rest of the word,
# given the halves the rest was cut into
law halve_two.put:
  for +h: Char
  for +t: String
  for +a: String
  for +b: String
  for r: Tgt.Halves
  for er: {Tgt.halve(t) == r : Tgt.Halves}
  for e: {Tgt.halve.put(h, r) == Tgt.Two{a, b} : Tgt.Halves}
  for ih: @x:String -> @y:String -> {Tgt.halve(t) == Tgt.Two{x, y} : Tgt.Halves}
    -> {t == x ++ ("/" ++ y) : String}
  {SCon{h, t} == a ++ ("/" ++ b) : String}

def halve_two.put(h, t, a, b, r, er, e, ih):
  match r:
    case Tgt.Uncut{}:
      Empty.absurd({SCon{h, t} == a ++ ("/" ++ b) : String}, uncut_two(a, b, e))
    case Tgt.Two{+x, +y}:
      +ee = e
      +el = Equal.cong(Tgt.Halves, String, v => two.left(v),
        Tgt.Two{SCon{h, x}, y}, Tgt.Two{a, b}, ee)
      +er2 = Equal.cong(Tgt.Halves, String, v => two.right(v),
        Tgt.Two{SCon{h, x}, y}, Tgt.Two{a, b}, ee)
      %el : {SCon{h, t} == _ ++ ("/" ++ b) : String}
      %er2 : {SCon{h, t} == SCon{h, x} ++ ("/" ++ _) : String}
      Equal.cong(String, String, v => SCon{h, v}, t, x ++ ("/" ++ y),
        ih(x, y, er))

# LAW: the char a word is cut at, with the five tests of its kind given as
# parameters
law halve_two.arm:
  for c: Bool
  for s: Bool
  for d: Bool
  for ti: Bool
  for w: Bool
  for +h: Char
  for +t: String
  for +a: String
  for +b: String
  for e: {Tgt.halve.at(Tgt.kind.colon(c, s, d, ti, w), h, t, _u => Tgt.halve(t))
    == Tgt.Two{a, b} : Tgt.Halves}
  for es: {Char.is_eq(h, '/') == s : Bool}
  for ih: @x:String -> @y:String -> {Tgt.halve(t) == Tgt.Two{x, y} : Tgt.Halves}
    -> {t == x ++ ("/" ++ y) : String}
  {SCon{h, t} == a ++ ("/" ++ b) : String}

def halve_two.arm(c, s, d, ti, w, h, t, a, b, e, es, ih):
  match c:
    case True{}:
      Empty.absurd({SCon{h, t} == a ++ ("/" ++ b) : String}, uncut_two(a, b, e))
    case False{}:
      match s:
        case True{}:
          +ee = e
          +el = Equal.cong(Tgt.Halves, String, v => two.left(v),
            Tgt.Two{"", t}, Tgt.Two{a, b}, ee)
          +er2 = Equal.cong(Tgt.Halves, String, v => two.right(v),
            Tgt.Two{"", t}, Tgt.Two{a, b}, ee)
          %el : {SCon{h, t} == _ ++ ("/" ++ b) : String}
          %er2 : {SCon{h, t} == "" ++ ("/" ++ _) : String}
          Equal.cong(Char, String, v => SCon{v, t}, h, '/', char_eq(h, '/', es))
        case False{}:
          match d:
            case True{}:
              halve_two.put(h, t, a, b, Tgt.halve(t), {==}, e, ih)
            case False{}:
              match ti:
                case True{}:
                  Empty.absurd({SCon{h, t} == a ++ ("/" ++ b) : String},
                    uncut_two(a, b, e))
                case False{}:
                  match w:
                    case True{}:
                      halve_two.put(h, t, a, b, Tgt.halve(t), {==}, e, ih)
                    case False{}:
                      Empty.absurd({SCon{h, t} == a ++ ("/" ++ b) : String},
                        uncut_two(a, b, e))

# LAW: a word cut into two halves is the halves around a slash
law halve_two:
  for +text: String
  for +a: String
  for +b: String
  for e: {Tgt.halve(text) == Tgt.Two{a, b} : Tgt.Halves}
  {text == a ++ ("/" ++ b) : String}

def halve_two(text, a, b, e):
  match text:
    case SNil{}:
      Empty.absurd({SNil{} == a ++ ("/" ++ b) : String}, uncut_two(a, b, e))
    case SCon{+h, +t}:
      halve_two.arm(Char.is_eq(h, ':'), Char.is_eq(h, '/'), Char.is_eq(h, '.'),
        Char.is_eq(h, '~'), Tgt.plain.at(h), h, t, a, b, e, {==},
        x => y => z => halve_two(t, x, y, z))

# LAW: the two halves' segments, with whether each is one given as a
# parameter
law github_no.two:
  for +text: String
  for +a: String
  for +b: String
  for x: Bool
  for ex: {Tgt.seg(a) == x : Bool}
  for y: Bool
  for ey: {Tgt.seg(b) == y : Bool}
  for z: Bool
  for ez: {Tgt.bend.file(b) == z : Bool}
  for et: {text == a ++ ("/" ++ b) : String}
  for no: @p:String -> @q:String -> {text == p ++ ("/" ++ q) : String}
    -> {Tgt.seg(p) == True{} : Bool} -> {Tgt.seg(q) == True{} : Bool}
    -> {Tgt.bend.file(q) == False{} : Bool} -> Empty
  {Bool.and(x, Bool.and(y, Bool.not(z))) == False{} : Bool}

def github_no.two(_text, a, b, x, ex, y, ey, z, ez, et, no):
  match x:
    case False{}:
      {==}
    case True{}:
      match y:
        case False{}:
          {==}
        case True{}:
          match z:
            case True{}:
              {==}
            case False{}:
              Empty.absurd({True{} == False{} : Bool}, no(a, b, et, ex, ey, ez))

# LAW: the halves a word was cut into, given as a parameter
law github_no.arm:
  for +text: String
  for r: Tgt.Halves
  for er: {Tgt.halve(text) == r : Tgt.Halves}
  for no: @p:String -> @q:String -> {text == p ++ ("/" ++ q) : String}
    -> {Tgt.seg(p) == True{} : Bool} -> {Tgt.seg(q) == True{} : Bool}
    -> {Tgt.bend.file(q) == False{} : Bool} -> Empty
  {Tgt.github.halves(r) == False{} : Bool}

def github_no.arm(text, r, er, no):
  match r:
    case Tgt.Uncut{}:
      {==}
    case Tgt.Two{+a, +b}:
      github_no.two(text, a, b, Tgt.seg(a), {==}, Tgt.seg(b), {==},
        Tgt.bend.file(b), {==},
        halve_two(text, a, b, er), no)

# LAW: a word that is not two segments around a slash is not a shorthand
law github_no:
  for +text: String
  for no: @p:String -> @q:String -> {text == p ++ ("/" ++ q) : String}
    -> {Tgt.seg(p) == True{} : Bool} -> {Tgt.seg(q) == True{} : Bool}
    -> {Tgt.bend.file(q) == False{} : Bool} -> Empty
  {Tgt.github.ok(text) == False{} : Bool}

def github_no(text, no):
  github_no.arm(text, Tgt.halve(text), {==}, no)

# LAW: a char after `~` or `..` that reads as a slash starts the rest with
# `/`, with the five tests of its kind given as parameters
law slash_starts.arm:
  for c: Bool
  for s: Bool
  for d: Bool
  for ti: Bool
  for w: Bool
  for +t: String
  for e: {Tgt.looks.slash.at(Tgt.kind.colon(c, s, d, ti, w)) == True{} : Bool}
  {String.starts_with.if(t, "", s) == True{} : Bool}

def slash_starts.arm(c, s, d, ti, w, t, e):
  match c:
    case True{}:
      Eq.bit.absurd(&2, {String.starts_with.if(t, "", s) == True{} : Bool}, e)
    case False{}:
      match s:
        case True{}:
          Eq.starts_nil(t)
        case False{}:
          match d:
            case True{}:
              Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)
            case False{}:
              match ti:
                case True{}:
                  Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)
                case False{}:
                  match w:
                    case True{}:
                      Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)
                    case False{}:
                      Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)

# LAW: a word the slash test passes starts with `/`
law slash_starts:
  for +t: String
  for e: {Tgt.looks.slash(t) == True{} : Bool}
  {String.starts_with(t, "/") == True{} : Bool}

def slash_starts(t, e):
  match t:
    case SNil{}:
      Eq.bit.absurd(&2, {String.starts_with(SNil{}, "/") == True{} : Bool}, e)
    case SCon{+h, +r}:
      slash_starts.arm(Char.is_eq(h, ':'), Char.is_eq(h, '/'), Char.is_eq(h, '.'),
        Char.is_eq(h, '~'), Tgt.plain.at(h), r, e)

# LAW: the char after a leading dot, with the five tests of its kind given as
# parameters: `./` or `../`
law dot_starts.arm:
  for c: Bool
  for s: Bool
  for d: Bool
  for ti: Bool
  for w: Bool
  for +t: String
  for z: Bool
  for e: {Tgt.looks.dot.at(Tgt.kind.colon(c, s, d, ti, w), t) == True{} : Bool}
  {Bool.or(String.starts_with.if(t, "", s),
    Bool.or(String.starts_with.if(t, "/", d), z)) == True{} : Bool}

def dot_starts.arm(c, s, d, ti, w, t, z, e):
  match c:
    case True{}:
      Eq.bit.absurd(&2, {Bool.or(String.starts_with.if(t, "", s),
        Bool.or(String.starts_with.if(t, "/", d), z)) == True{} : Bool}, e)
    case False{}:
      match s:
        case True{}:
          %Equal.sym(Bool, String.starts_with(t, ""), True{}, Eq.starts_nil(t)) :
            {Bool.or(_, Bool.or(String.starts_with.if(t, "/", d), z)) == True{}
              : Bool}
          {==}
        case False{}:
          match d:
            case True{}:
              %Equal.sym(Bool, String.starts_with(t, "/"), True{},
                slash_starts(t, e)) : {Bool.or(_, z) == True{} : Bool}
              {==}
            case False{}:
              match ti:
                case True{}:
                  Eq.bit.absurd(&2, {Bool.or(False{}, z) == True{} : Bool}, e)
                case False{}:
                  match w:
                    case True{}:
                      Eq.bit.absurd(&2, {Bool.or(False{}, z) == True{} : Bool}, e)
                    case False{}:
                      Eq.bit.absurd(&2, {Bool.or(False{}, z) == True{} : Bool}, e)

# LAW: a word the dot test passes starts with `/` or `./`, whatever else is
# asked beside them
law dot_starts:
  for +t: String
  for z: Bool
  for e: {Tgt.looks.dot(t) == True{} : Bool}
  {Bool.or(String.starts_with(t, "/"), Bool.or(String.starts_with(t, "./"), z))
    == True{} : Bool}

def dot_starts(t, z, e):
  match t:
    case SNil{}:
      Eq.bit.absurd(&2, {Bool.or(False{}, Bool.or(False{}, z)) == True{} : Bool}, e)
    case SCon{+h, +r}:
      dot_starts.arm(Char.is_eq(h, ':'), Char.is_eq(h, '/'), Char.is_eq(h, '.'),
        Char.is_eq(h, '~'), Tgt.plain.at(h), r, z, e)

# LAW: a word's first char, with the five tests of its kind given as
# parameters
law path_starts.arm:
  for c: Bool
  for s: Bool
  for d: Bool
  for ti: Bool
  for w: Bool
  for +t: String
  for e: {Tgt.looks.first(Tgt.kind.colon(c, s, d, ti, w), t) == True{} : Bool}
  {Bool.or(String.starts_with.if(t, "", s),
    Bool.or(String.starts_with.if(t, "/", d),
      Bool.or(String.starts_with.if(t, "./", d),
        String.starts_with.if(t, "/", ti)))) == True{} : Bool}

def path_starts.arm(c, s, d, ti, w, t, e):
  match c:
    case True{}:
      Eq.bit.absurd(&2, {Bool.or(String.starts_with.if(t, "", s),
        Bool.or(String.starts_with.if(t, "/", d),
          Bool.or(String.starts_with.if(t, "./", d),
            String.starts_with.if(t, "/", ti)))) == True{} : Bool}, e)
    case False{}:
      match s:
        case True{}:
          %Equal.sym(Bool, String.starts_with(t, ""), True{}, Eq.starts_nil(t)) :
            {Bool.or(_, Bool.or(String.starts_with.if(t, "/", d),
              Bool.or(String.starts_with.if(t, "./", d),
                String.starts_with.if(t, "/", ti)))) == True{} : Bool}
          {==}
        case False{}:
          match d:
            case True{}:
              dot_starts(t, String.starts_with.if(t, "/", ti), e)
            case False{}:
              match ti:
                case True{}:
                  slash_starts(t, e)
                case False{}:
                  match w:
                    case True{}:
                      Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)
                    case False{}:
                      Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)

# LAW: a word the path test passes starts `/`, `./`, `../` or `~/`
law path_starts:
  for +text: String
  for e: {Tgt.looks.path(text) == True{} : Bool}
  {Bool.or(String.starts_with(text, "/"),
    Bool.or(String.starts_with(text, "./"),
      Bool.or(String.starts_with(text, "../"),
        String.starts_with(text, "~/")))) == True{} : Bool}

def path_starts(text, e):
  match text:
    case SNil{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, e)
    case SCon{+h, +t}:
      path_starts.arm(Char.is_eq(h, ':'), Char.is_eq(h, '/'), Char.is_eq(h, '.'),
        Char.is_eq(h, '~'), Tgt.plain.at(h), t, e)

# LAW: a word starting none of the four does not look like a path
law path_none:
  for +text: String
  for e1: {False{} == String.starts_with(text, "/") : Bool}
  for e2: {False{} == String.starts_with(text, "./") : Bool}
  for e3: {False{} == String.starts_with(text, "../") : Bool}
  for e4: {False{} == String.starts_with(text, "~/") : Bool}
  {False{} == Bool.or(String.starts_with(text, "/"),
    Bool.or(String.starts_with(text, "./"),
      Bool.or(String.starts_with(text, "../"),
        String.starts_with(text, "~/")))) : Bool}

def path_none(text, e1, e2, e3, e4):
  %e1 : {False{} == Bool.or(_, Bool.or(String.starts_with(text, "./"),
    Bool.or(String.starts_with(text, "../"), String.starts_with(text, "~/"))))
    : Bool}
  %e2 : {False{} == Bool.or(False{}, Bool.or(_,
    Bool.or(String.starts_with(text, "../"), String.starts_with(text, "~/"))))
    : Bool}
  %e3 : {False{} == Bool.or(False{}, Bool.or(False{},
    Bool.or(_, String.starts_with(text, "~/")))) : Bool}
  %e4 : {False{} == Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _)))
    : Bool}
  {==}

# LAW: the path test's answer, given as a parameter
law path_no.arm:
  for +text: String
  for l: Bool
  for el: {Tgt.looks.path(text) == l : Bool}
  for e1: {False{} == String.starts_with(text, "/") : Bool}
  for e2: {False{} == String.starts_with(text, "./") : Bool}
  for e3: {False{} == String.starts_with(text, "../") : Bool}
  for e4: {False{} == String.starts_with(text, "~/") : Bool}
  {l == False{} : Bool}

def path_no.arm(text, l, el, e1, e2, e3, e4):
  match l:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.trans(Bool, False{},
          Bool.or(String.starts_with(text, "/"),
            Bool.or(String.starts_with(text, "./"),
              Bool.or(String.starts_with(text, "../"),
                String.starts_with(text, "~/")))),
          True{}, path_none(text, e1, e2, e3, e4), path_starts(text, el)))

# LAW: a word starting none of the four is not read as a path
law path_no:
  for +text: String
  for e1: {False{} == String.starts_with(text, "/") : Bool}
  for e2: {False{} == String.starts_with(text, "./") : Bool}
  for e3: {False{} == String.starts_with(text, "../") : Bool}
  for e4: {False{} == String.starts_with(text, "~/") : Bool}
  {Tgt.looks.path(text) == False{} : Bool}

def path_no(text, e1, e2, e3, e4):
  path_no.arm(text, Tgt.looks.path(text), {==}, e1, e2, e3, e4)

def Laws.classify_else(text, ne, eu, eg, e1, e2, e3, e4, no):
  %ne : {Tgt.classify.empty(_, text) == Tgt.Local{text} : Tgt.Place}
  %eu : {Tgt.classify.url(_, text) == Tgt.Local{text} : Tgt.Place}
  %Equal.sym(Bool, Tgt.looks.path(text), False{}, path_no(text, e1, e2, e3, e4)) :
    {Tgt.classify.path(_, text) == Tgt.Local{text} : Tgt.Place}
  %Equal.sym(Bool, Tgt.github.ok(text), False{}, github_no(text, no)) :
    {Tgt.classify.hub(_, text) == Tgt.Local{text} : Tgt.Place}
  %eg : {Tgt.classify.scp(_, text) == Tgt.Local{text} : Tgt.Place}
  {==}

def Laws.target_escapes():
  {==}

# `~/` is not `~`, which computes, and is a prefix of what it was put on,
# which `starts_nil` holds for the open rest
def Laws.expand_home(home, rest):
  %Equal.sym(Bool, String.starts_with(rest, ""), True{}, Eq.starts_nil(rest)) :
    {Bool.pick(String, _, home ++ String.drop("~/" ++ rest, 1n), "~/" ++ rest)
      == home ++ ("/" ++ rest) : String}
  {==}

def Laws.file_bin():
  {==}

def Laws.file_entry():
  {==}

def Laws.file_default():
  {==}

def Laws.out_name_empty():
  {==}

def Laws.out_name():
  {==}

# `.ez/` is a prefix of anything appended to it, which `starts_append` holds,
# and that picks the arm that keeps nothing.
def Laws.root_skips_ez(p):
  Equal.cong(Bool, List<&2, String>,
    k => Bool.pick(List<&2, String>, k, [], [".ez/" ++ p]),
    String.starts_with(".ez/" ++ p, ".ez/"), True{}, Eq.starts_append(".ez/", p))

# A ledger that is there picks the arm that plans nothing.
def Laws.init_keeps_ledger(_s, _name, _at):
  {==}

# named: a walk from the end of a text has passed a slash once it has passed
# the one in front of `n`, and nothing to its left changes that. The name laws
# rewrite the one `String.eq` each branch turns on.

# LAW: past the slash in front of a slashless `n`, the walk has seen a slash
# and kept `n`, whatever is to the left of it
law last_after:
  for p: String
  for +n: String
  for e: {Named.Seen{False{}, n} == Named.last(n) : Named.Seen}
  {Named.last(p ++ ("/" ++ n)) == Named.Seen{True{}, n} : Named.Seen}

def last_after(p, n, e):
  match p:
    case SNil{}:
      %e : {Named.last.step('/', _) == Named.Seen{True{}, n} : Named.Seen}
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Named.Seen, Named.last(t ++ ("/" ++ n)), Named.Seen{True{}, n},
        last_after(t, n, e)) :
        {Named.last.step(h, _) == Named.Seen{True{}, n} : Named.Seen}
      {==}

def Laws.leaf_is_last(p, n, e):
  Equal.cong(Named.Seen, String, Named.leaf.of,
    Named.last(p ++ ("/" ++ n)), Named.Seen{True{}, n}, last_after(p, n, e))

def Laws.had_fresh(_url, _fresh):
  {==}

def Laws.had_keeps(n, _h, _en, url, _rev, _tag, _root, _nar, _vend, t, fresh):
  %Equal.sym(Bool, String.eq(url, url), True{}, Eq.string_eq_self(url)) :
    {Named.had.at(_, n, Named.had(t, url, fresh)) == n : String}
  {==}

def Laws.had_skips_git(n, _h, _en, _u, url, _rev, _tag, _root, _nar, _vend, t, fresh, ne):
  %ne : {Named.had.at(_, n, Named.had(t, url, fresh)) == Named.had(t, url, fresh)
    : String}
  {==}

def Laws.had_skips_hub(_n, _h, _en, _url, _t, _fresh):
  {==}

def Laws.clash_none(_name, _url):
  {==}

def Laws.clash_skips(_m, _h, _en, s, t, name, url, ne):
  %ne : {Named.clash.at(_, s, url, Named.clash(t, name, url))
    == Named.clash(t, name, url) : Bool}
  {==}

def Laws.clash_same(n, _h, _en, url, rev, tag, root, nar, vend, t):
  %Equal.sym(Bool, String.eq(n, n), True{}, Eq.string_eq_self(n)) :
    {Named.clash.at(_, M.Git{url, rev, tag, root, nar, vend}, url,
      Named.clash(t, n, url)) == False{} : Bool}
  %Equal.sym(Bool, String.eq(url, url), True{}, Eq.string_eq_self(url)) :
    {Bool.not(_) == False{} : Bool}
  {==}

def Laws.clash_other(n, _h, _en, u, url, rev, tag, root, nar, vend, t, ne):
  %Equal.sym(Bool, String.eq(n, n), True{}, Eq.string_eq_self(n)) :
    {Named.clash.at(_, M.Git{u, rev, tag, root, nar, vend}, url,
      Named.clash(t, n, url)) == True{} : Bool}
  %ne : {Bool.not(_) == True{} : Bool}
  {==}

def Laws.clash_hub(n, _h, _en, url, t):
  %Equal.sym(Bool, String.eq(n, n), True{}, Eq.string_eq_self(n)) :
    {Named.clash.at(_, M.Hub{}, url, Named.clash(t, n, url)) == True{} : Bool}
  {==}

# A pin's two emptiness tests are rewritten to the False each premise gives,
# and what is left is the arm that passes or the reason written out.
def Laws.gap_of_full_pin(n, _e, _b, _url, _rev, _tag, _root, nar, _vend, fr, fn):
  %fr : {Pin.gap.git(_, String.is_empty(nar), n) == "" : String}
  %fn : {Pin.gap.git(False{}, _, n) == "" : String}
  {==}

def Laws.gap_of_revless_pin(_n, _e, _b, _url, _tag, _root, _nar, _vend):
  {==}

def Laws.gap_of_narless_pin(n, _e, _b, _url, _rev, _tag, _root, _vend, fr):
  %fr : {Pin.gap.git(_, True{}, n) == "ez: tools." ++ n ++
    " has no narHash; run `ez lock --upgrade --package " ++ n ++ "` to pin it"
    : String}
  {==}
