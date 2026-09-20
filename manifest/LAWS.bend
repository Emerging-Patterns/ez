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
