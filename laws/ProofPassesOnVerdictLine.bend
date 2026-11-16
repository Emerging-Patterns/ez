# `ez prove` passes a proof exactly when the first line its run printed is
# `ALL PROOFS CHECK`, and counts one more pass for each proof that passed and
# none for one that did not. A run that printed anything else first fails,
# whatever it printed after. What a failed run printed is shown indented, one
# line of it per line. This is internal: it fixes how ez/verdict.bend reads
# a run, which ez/prove.bend trusts; that the runner hands it what bend
# printed is trusted in ez/prove.bend. Each file the runners found gets one
# `bend` run, in the order they found them.
import Base
import ../src/ez/verdict.bend as V

# LAW: a run whose first line is the verdict passes
law passes_on_verdict:
  for text: String
  for t: List<&2, String>
  for e: {"ALL PROOFS CHECK" <> t == String.lines(text) : List<&2, String>}
  {V.passed(text) == True{} : Bool}

# LAW: and a run whose first line is anything else fails
law fails_otherwise:
  for text: String
  for +h: String
  for t: List<&2, String>
  for e: {h <> t == String.lines(text) : List<&2, String>}
  for ne: {False{} == String.eq(h, V.verdict()) : Bool}
  {V.passed(text) == False{} : Bool}

# LAW: a pass counts one more
law count_pass:
  for +n: Nat
  {V.count(True{}, n) == (1n + n : Nat) : Nat}

# LAW: and a failure counts none
law count_fail:
  for +n: Nat
  {V.count(False{}, n) == n : Nat}

# LAW: what a failed run printed is shown a line at a time, each indented
law indent_lines:
  for text: String
  for +h: String
  for t: List<&2, String>
  for e: {h <> t == String.lines(text) : List<&2, String>}
  {V.indent(text) == String.append("    " ++ h ++ "\n", String.concat(V.indent.go(t)))
    : String}

# LAW: the runners start one `bend` for every file they found
law one_run_per_file:
  for ps: List<&2, String>
  for +cap: Bool
  for +gigs: String
  for +at: String
  {List.length(&2, List<&2, String>, V.cmds(ps, cap, gigs, at)) == List.length(&2, String, ps) : Nat}
