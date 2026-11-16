# proofs of laws/NarHashForm.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/sha/nar.bend as Nar
import ../src/share/sha.bend as Sha
import ../laws/NarHashForm.bend as Laws

def Laws.nar_archive_magic(_node):
  {==}

# the SRI is `sha256-` appended to the base64, so it is a prefix
def Laws.sri_names_sha256(bytes):
  Eq.starts_append("sha256-", Nar.b64(Nar.hex.bytes(Sha.raw(bytes))))

# the group's own encoding, with the empty rest it ends on taken off
def Laws.b64_by_groups_of_three(a, b, c, rest):
  Equal.cong(String, String, x => String.append(x, Nar.b64(rest)),
    Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)),
    String.append(Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)), ""),
    Equal.sym(String,
      String.append(Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)), ""),
      Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)),
      Eq.append_nil(Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)))))

# each padded group is four characters built one by one
def Laws.b64_pads_one(_a):
  {==}

def Laws.b64_pads_two(_a, _b):
  {==}

# a triple is four characters, and the empty rest adds none
def Laws.b64_three_is_four(a, b, c):
  Equal.cong(String, Nat, x => String.length(x),
    String.append(Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)), ""),
    Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)),
    Eq.append_nil(Nar.b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c))))
