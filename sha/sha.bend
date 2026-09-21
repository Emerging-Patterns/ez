# sha/sha: the sha256 a package hash is built from. The digest itself comes from
# Giulio2002/bend-sha256, which proves its output equal to an executable FIPS
# 180-4 specification; this file is only the string-in, hex-out shape ez uses.
# The dependency hashes packed big-endian words and returns eight of them, or
# nothing when the declared length does not fit the array.
import Base
import 0x33de775bd13bab25b3e2d6f5bbcb8776/sha256.bend as S

# four big-endian bytes in one word, each kept to eight bits
def pack(a: U32, b: U32, c: U32, d: U32) -> U32:
  (U32.shln((a .&. 255 : U32), 24n)
    .|. U32.shln((b .&. 255 : U32), 16n)
    .|. U32.shln((c .&. 255 : U32), 8n) .|. (d .&. 255) : U32)

# one character as the byte it contributes
def byte(c: Char) -> U32:
  Char.to_u32(c)

# how many words hold this many bytes
def words.of(n: Nat) -> Nat:
  Nat.div(Nat.add(n, 3n), 4n)

# one more bit of depth when the capacity does not yet hold the words. The
# rest is a thunk, so the stop does not build the next depth.
def depth.step(more: Bool, acc: Nat, rest: Unit -> Nat) -> Nat:
  match more:
    case False{}:
      acc
    case True{}:
      rest(Unit{})

# the depth of an array whose capacity, 2^depth, is at least `words`
def depth.go(fuel: Nat, +words: Nat, +cap: Nat, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      depth.step(Nat.is_lt(cap, words), acc,
        _u => depth.go(p, words, Nat.mul(cap, 2n), Nat.add(acc, 1n)))

def depth(words: Nat) -> Nat:
  depth.go(32n, words, 1n, 0n)

# the string packed into the array, four bytes to a word. A short tail packs
# zeros in the unused bytes; the byte length says they are padding. The walk
# calls itself on the tail, which is the string shrinking.
def fill(s: String, +i: U32, a: Array<U32>) -> Array<U32>:
  match s:
    case SNil{}:
      a
    case SCon{w, SNil{}}:
      Array.set(U32, a, i, pack(byte(w), 0, 0, 0))
    case SCon{w, SCon{x, SNil{}}}:
      Array.set(U32, a, i, pack(byte(w), byte(x), 0, 0))
    case SCon{w, SCon{x, SCon{y, SNil{}}}}:
      Array.set(U32, a, i, pack(byte(w), byte(x), byte(y), 0))
    case SCon{w, SCon{x, SCon{y, SCon{z, t}}}}:
      fill(t, U32.inc(i), Array.set(U32, a, i, pack(byte(w), byte(x), byte(y), byte(z))))

# the string packed into big-endian words, four bytes each
def bytes(+s: String) -> Array<U32>:
  +n = String.length(s)
  fill(s, 0, Array.new(U32, depth(words.of(n)), 0))

# a length that does not fit is not a digest. A digest is sixty-four hex
# characters, so this empty answer cannot be mistaken for one.
def show(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{}:
      ""
    case Some{digest}:
      S.hex(digest)

# the hex sha256 digest of a string's bytes. The match is what a symbolic
# string sticks on, so a proof that only unfolds `hash_of` does not enter
# the digest.
def hex(+s: String) -> String:
  match s:
    case SNil{}:
      show(S.sha256(bytes(s), 0n))
    case SCon{_c, _t}:
      show(S.sha256(bytes(s), String.length(s)))
