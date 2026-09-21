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

def Laws.filter_empty():
  {==}

def Laws.filter_old_report():
  {==}

def Laws.filter_new_report():
  {==}

def Laws.filter_keeps_own_dash():
  {==}

def Laws.filter_untouched():
  {==}

def Laws.chomp_trailing():
  {==}

def Laws.chomp_keeps_inner_blank():
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

def Laws.trailer_extracts():
  {==}

def Laws.trailer_empty():
  {==}

def Laws.trailer_ignores_note():
  {==}

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

def Laws.at_root():
  {==}

def Laws.at_under(d, e):
  %e : {Bool.pick(String, _, G.root(), G.root() ++ "/" ++ d)
    == G.root() ++ "/" ++ d : String}
  {==}

def Laws.proj_one():
  {==}

def Laws.proj_top():
  {==}

def Laws.proj_deep():
  {==}

def Laws.src_place():
  {==}

def Laws.levels_of_two():
  {==}

def Laws.linked_keeps_bin():
  {==}

def Laws.agg_imports_local():
  {==}

def Laws.agg_calls_behind_mark():
  {==}

def Laws.slice_first():
  {==}

def Laws.slice_last():
  {==}

def Laws.slice_miss():
  {==}

def Laws.started_yes():
  {==}

def Laws.started_no():
  {==}

def Laws.headed_line():
  {==}

def Laws.headed_quoted():
  {==}

def Laws.solitary_reads_args():
  {==}

def Laws.solitary_comment_only():
  {==}
