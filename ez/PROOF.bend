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

# LAW: and the same for the `./` a find path opens with
law drop_dot_slash:
  for +rest: String
  {String.drop("./" ++ rest, 2n) == rest : String}

def drop_dot_slash(rest):
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

def Laws.rel_plain(p, e):
  %e : {Bool.pick(String, _, String.drop(p, 2n), p) == p : String}
  {==}

def Laws.rel_dot(rest):
  Equal.trans(String,
    Bool.pick(String, String.starts_with(String.append("./", rest), "./"),
      String.drop(String.append("./", rest), 2n), String.append("./", rest)),
    Bool.pick(String, True{}, String.drop(String.append("./", rest), 2n),
      String.append("./", rest)),
    rest,
    Equal.cong(Bool, String,
      x => Bool.pick(String, x, String.drop(String.append("./", rest), 2n),
        String.append("./", rest)),
      String.starts_with(String.append("./", rest), "./"), True{},
      Eq.starts_append("./", rest)),
    drop_dot_slash(rest))

def Laws.at_under(d, e):
  %e : {Bool.pick(String, _, G.root(), G.root() ++ "/" ++ d)
    == G.root() ++ "/" ++ d : String}
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

def Laws.target_github():
  {==}

def Laws.target_url():
  {==}

def Laws.target_scp():
  {==}

def Laws.target_abs():
  {==}

def Laws.target_file():
  {==}

def Laws.target_dot():
  {==}

def Laws.target_empty():
  {==}

def Laws.target_escapes():
  {==}

def Laws.expand_tilde():
  {==}

def Laws.expand_plain():
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
