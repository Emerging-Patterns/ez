# proofs of laws/ProgressNamesBriefly.bend
import Base
import ../src/pkg/path.bend as P
import ../src/share/say.bend as Say
import ../laws/ProgressNamesBriefly.bend as Laws

# each is the branch its premise picks
def Laws.short_rev_whole(rev, short):
  Equal.cong(Bool, String, b => Say.brief.go(b, rev),
    Nat.is_le(String.length(rev), 12n), True{}, short)

def Laws.long_rev_cut(rev, long):
  Equal.cong(Bool, String, b => Say.brief.go(b, rev),
    Nat.is_le(String.length(rev), 12n), False{}, long)

def Laws.label_names_entry(hash, entry, named):
  Equal.cong(Bool, String, b => Say.label.go(b, hash, P.unbend(P.base(entry))),
    String.is_empty(P.unbend(P.base(entry))), False{}, named)

def Laws.label_falls_to_hash(hash, entry, blank):
  Equal.cong(Bool, String, b => Say.label.go(b, hash, P.unbend(P.base(entry))),
    String.is_empty(P.unbend(P.base(entry))), True{}, blank)
