# proofs of laws/PublishUnderName.bend
import Base
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/git/git.bend as Git
import ../laws/PublishAgreesWithBend.bend as L1
import ../laws/PublishUnderName.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1

# ---------------------------------------------------------------------------
# the name a package is published under

# LAW: an `and` with False on its right is False
law and_false_pub:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def and_false_pub(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a character that is neither a digit nor a dot, after any stretch of a
# version, sinks the walk over its characters
law chars_sink:
  for +pre: String
  for +c: Char
  for +post: String
  for e: {False{} == PP.semver.char(c) : Bool}
  {PP.semver.chars(String.append(pre, SCon{c, post})) == False{} : Bool}

# by induction on the stretch: at its end the character answers False, and
# every character before it ands its own answer with that False
def chars_sink(pre, c, post, e):
  match pre:
    case SNil{}:
      %e : {Bool.and(_, PP.semver.chars(post)) == False{} : Bool}
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, PP.semver.chars(String.append(t, SCon{c, post})), False{},
        chars_sink(t, c, post, e))
        : {Bool.and(PP.semver.char(h), _) == False{} : Bool}
      and_false_pub(PP.semver.char(h))

# The walk over the characters comes first in `semver`, so its False ends it.
def Laws.semver_needs_digits(pre, c, post, e):
  %Equal.sym(Bool, PP.semver.chars(String.append(pre, SCon{c, post})), False{},
    chars_sink(pre, c, post, e))
    : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, String,
        String.split(String.append(pre, SCon{c, post}), '.')), 3n),
        K.ver.nums(String.split(String.append(pre, SCon{c, post}), '.')))) == False{} : Bool}
  {==}

# `-` and `+` are neither digits nor dots, which computes.
def Laws.prerelease_refused(pre, post):
  Laws.semver_needs_digits(pre, '-', post, {==})

def Laws.build_refused(pre, post):
  Laws.semver_needs_digits(pre, '+', post, {==})

# Each emptiness test, and each check of a name and a version, is rewritten to
# the answer its premise gives, and `naming` computes to the arm it picks.
def Laws.neither_is_hash(pa, pv, e0, e1):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.ByHash{} : PP.Named}
  %e1 : {PP.naming.go(True{}, _, pa, pv) == PP.ByHash{} : PP.Named}
  {==}

def Laws.name_needs_version(pa, pv, e0, e1):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.nover(pa)}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.Unnamed{PP.why.nover(pa)} : PP.Named}
  {==}

def Laws.version_needs_name(pa, pv, e0, e1):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.noname(pv)}
    : PP.Named}
  %e1 : {PP.naming.go(True{}, _, pa, pv) == PP.Unnamed{PP.why.noname(pv)} : PP.Named}
  {==}

def Laws.bad_name_refused(pa, pv, e0, e1, en):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.name(pa)}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.Unnamed{PP.why.name(pa)} : PP.Named}
  %en : {PP.naming.both(_, PP.semver(pv), pa, pv) == PP.Unnamed{PP.why.name(pa)} : PP.Named}
  {==}

def Laws.bad_version_refused(pa, pv, e0, e1, en, ev):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.Unnamed{PP.why.ver(pv)}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}
  %en : {PP.naming.both(_, PP.semver(pv), pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}
  %ev : {PP.naming.both(True{}, _, pa, pv) == PP.Unnamed{PP.why.ver(pv)} : PP.Named}
  {==}

def Laws.named_is_four_part(pa, pv, e0, e1, en, ev):
  %e0 : {PP.naming.go(_, String.is_empty(pv), pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"}
    : PP.Named}
  %e1 : {PP.naming.go(False{}, _, pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"} : PP.Named}
  %en : {PP.naming.both(_, PP.semver(pv), pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"}
    : PP.Named}
  %ev : {PP.naming.both(True{}, _, pa, pv) == PP.ByName{pa ++ "@" ++ pv ++ ".0"} : PP.Named}
  {==}

def Laws.upload_by_hash(_entry):
  {==}

def Laws.upload_by_name(entry, nv, e):
  %e : {PP.upload.go(_, entry, nv) == ["bend", entry, "--publish", nv] : List<&2, String>}
  {==}

# ---------------------------------------------------------------------------
# the name, through the planner: the ledger's text is rewritten to the model
# it parses as, and the naming of its two keys to the answer the premise
# gives, and the stage computes

def Laws.pub_misnamed_stops(here, text, rs, n, e, b, h, pa, pv, ds, ts, why, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.stops.v(PP.decide.led(PP.led.read(_), PW.World{here, Some{text}, rs})) == True{} : Bool}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.Unnamed{why}, u)
    : {PP.stops.v(PP.decide.led(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _), PW.World{here,
      Some{text}, rs})) == True{} : Bool}
  {==}

def Laws.pub_named_uploads_named(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}),
      PP.named.word(PP.named.of(PP.led.read(_))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), nv, PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByName{nv}, u)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), PP.named.word(PP.named.of(PP.led.named(Bool.pick(String,
      String.is_empty(e), "main.bend", e), _))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), nv, PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  {==}

def Laws.pub_unnamed_uploads_by_hash(here, text, rs, n, e, b, h, pa, pv, ds, ts, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}),
      PP.named.word(PP.named.of(PP.led.read(_))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), "", PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByHash{}, u)
    : {PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), PP.named.word(PP.named.of(PP.led.named(Bool.pick(String,
      String.is_empty(e), "main.bend", e), _))), PP.said(PW.World{here, Some{text}, rs})}
      == PW.Upload{PP.entry(PW.World{here, Some{text}, rs}), "", PP.said(PW.World{here, Some{text}, rs})} : PW.Ask}
  {==}

# LAW: a World whose ledger names the package calls it by that name
law called_named:
  for +here: String
  for +text: String
  for +rs: List<&2, PW.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +pa: String
  for +pv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +nv: String
  for g: {M.parse(text) == M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}} : M.Read}
  for u: {PP.naming(pa, pv) == PP.ByName{nv} : PP.Named}
  {PP.called(PW.World{here, Some{text}, rs}) == nv : String}

def called_named(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g, u):
  %Equal.sym(M.Read, M.parse(text), M.Good{M.Manifest{n, e, b, h, pa, pv, ds, ts}}, g)
    : {PP.called.of(PP.named.of(PP.led.read(_)), PP.hash(PW.World{here, Some{text}, rs})) == nv : String}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByName{nv}, u)
    : {PP.called.of(PP.named.of(PP.led.named(Bool.pick(String, String.is_empty(e), "main.bend", e), _)),
      PP.hash(PW.World{here, Some{text}, rs})) == nv : String}
  {==}

# What a publish that succeeds says (`pub_reports_ours`), with what it calls
# the package rewritten to the name or the hash.
def Laws.pub_reports_name(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g, u, ok):
  Equal.trans(List<&2, String>, P.said(PP.plan(PW.World{here, Some{text}, rs})),
    [PP.hash(PW.World{here, Some{text}, rs}), Git.import.line(PP.called(PW.World{here, Some{text}, rs}),
      PP.at(PW.World{here, Some{text}, rs}))],
    [PP.hash(PW.World{here, Some{text}, rs}), Git.import.line(nv, PP.at(PW.World{here, Some{text}, rs}))],
    L1.pub_reports_ours(PW.World{here, Some{text}, rs}, ok),
    Equal.cong(String, List<&2, String>,
      x => [PP.hash(PW.World{here, Some{text}, rs}), Git.import.line(x, PP.at(PW.World{here, Some{text}, rs}))],
      PP.called(PW.World{here, Some{text}, rs}), nv, called_named(here, text, rs, n, e, b, h, pa, pv, ds, ts, nv, g,
        u)))

def Laws.init_publishes_by_hash(_n, _e):
  {==}
