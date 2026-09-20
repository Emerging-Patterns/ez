# manifest: the laws. The human states them; PROOF.bend must prove them. The
# ledger is a file a person edits, so what matters is that a lookup answers
# with what was written for it, and that the two edits `ez add` and
# `ez remove` make are the edits they claim to be.
import Base
import ./toml.bend as T
import ./manifest.bend as M
import ./render.bend as R

# LAW: a table answers a key with the value written for it, whatever pairs
# follow. A later pair of the same name never shadows an earlier one.
law value_first:
  for +k: String
  for v: String
  for ps: List<&2, T.Kv>
  {T.value(T.Kv{k, v} <> ps, k) == v : String}

# LAW: whatever a ledger quotes, the parser takes back out of the quotes
# unchanged. `ez.lock.toml` writes every value quoted and a file path as a
# quoted key, so this round trip is what makes a lock readable by the writer.
law quote_strip:
  for +s: String
  {T.strip(T.quote(s), '"', '"') == s : String}

# LAW: dropping a dependency drops every entry of that name, so dropping twice
# is dropping once. `ez remove` on a ledger it already edited is a no-op.
law without_idem:
  for ds: List<&2, M.Dep>
  for +name: String
  {R.without(R.without(ds, name), name) == R.without(ds, name) : List<&2, M.Dep>}

# LAW: adding a dependency twice is adding it once, which is what makes
# `ez add` safe to run on a ledger that already names the package.
law add_idem:
  for m: M.Manifest
  for +d: M.Dep
  {R.add(R.add(m, d), d) == R.add(m, d) : M.Manifest}

# The shapes manifest/toml.bend had before this pass rewrote them for cost,
# kept here so that the rewrites' one real risk can be stated rather than
# sampled: that the cheaper definitions answer exactly what the old ones
# answered, on every input. These are the specification and toml.bend is the
# implementation, the way net/LAWS.bend keeps the shapes net/http.bend had
# before its dechunk rewrite. Nothing but the laws below reads them.
#
# What was wrong with them is not what they answer, it is what they cost.
# `Bool.pick`, `Bool.and` and `Bool.or` are ordinary functions, so every arm
# and both sides are reduced before the answer is chosen.

# the line classifier, before: four picks nested, so `head_of(s, ...)` and
# `pair_of(String.split(s, '='))` were built for every line of every manifest
# and every lock ez reads, including the blanks and the comments the first two
# arms exist to answer
def old.line_of(+s: String) -> T.Line:
  Bool.pick(T.Line, String.is_empty(s), T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
      Bool.pick(T.Line, String.starts_with(s, "["),
        T.head_of(s, String.ends_with(s, "]")),
        Bool.pick(T.Line, String.contains(s, "="),
          T.pair_of(String.split(s, '=')),
          T.LBad{s ++ " is neither a section header nor a key"}))))

# the bare-key walk, before: `Bool.and` runs both sides, so the first char a
# bare key may not hold still cost a walk of the rest of the key
def old.bare.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      Bool.and(T.bare.at(h), old.bare.all(t))

# LAW: the cascade of matches answers what the nest of picks answered, on
# every line. This is the whole risk of the rewrite, and it is not a
# theoretical one: the nest tests for a blank line first, and a cascade that
# dropped that test would call an empty line neither a header nor a key.
# manifest/bench/parse.bend puts the saving at 1.95x over a lock of seven
# hundred thousand lines.
law line_of_agrees:
  for +s: String
  {old.line_of(s) == T.line_of(s) : T.Line}

# LAW: and the walk that now really does stop at the first char a bare key
# may not hold answers what the walk that did not stop answered
law bare_all_agrees:
  for cs: List<&2, Char>
  {old.bare.all(cs) == T.bare.all(cs) : Bool}
