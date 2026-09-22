# sha: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./sha.bend as Sha
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# by induction on the left text: its first character's bytes lead both sides,
# and the rest is the law again once the append is reassociated
def Laws.utf8_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(String,
        String.append(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(String.append(t, b))),
        String.append(Sha.utf8.put(Char.to_u32(h)),
          String.append(Sha.utf8(t), Sha.utf8(b))),
        String.append(String.append(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(t)),
          Sha.utf8(b)),
        Equal.cong(String, String, x => String.append(Sha.utf8.put(Char.to_u32(h)), x),
          Sha.utf8(String.append(t, b)),
          String.append(Sha.utf8(t), Sha.utf8(b)),
          Laws.utf8_append(t, b)),
        Equal.sym(String,
          String.append(String.append(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(t)),
            Sha.utf8(b)),
          String.append(Sha.utf8.put(Char.to_u32(h)),
            String.append(Sha.utf8(t), Sha.utf8(b))),
          Eq.append_assoc(Sha.utf8.put(Char.to_u32(h)), Sha.utf8(t), Sha.utf8(b))))
