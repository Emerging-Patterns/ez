# sha/sha: the sha256 a package hash is built from. The digest itself comes from
# Giulio2002/bend-sha256, which proves its output equal to an executable FIPS
# 180-4 specification; this file is only the string-in, hex-out shape ez uses.
# The dependency hashes packed big-endian words and returns eight of them, or
# nothing when the declared length does not fit the array.
import Base
import 0xda83506fb9f059ead7afcfa2f498df5f/sha256.bend as S

# four big-endian bytes in one word, each kept to eight bits
def pack(first: U32, second: U32, third: U32, fourth: U32) -> U32:
  (U32.shln((first .&. 255 : U32), 24n)
    .|. U32.shln((second .&. 255 : U32), 16n)
    .|. U32.shln((third .&. 255 : U32), 8n) .|. (fourth .&. 255) : U32)

# one character as the byte it contributes
def byte(ch: Char) -> U32:
  Char.to_u32(ch)

# how many words hold this many bytes
def words.of(len: Nat) -> Nat:
  Nat.div(Nat.add(len, 3n), 4n)

# one more bit of depth when the capacity does not yet hold the words. The
# rest is a thunk, so the stop does not build the next depth.
def depth.step(more: Bool, acc: Nat, rest: Unit -> Nat) -> Nat:
  match more:
    case False{}:
      acc
    case True{}:
      rest(Unit{})

# the depth of an array whose capacity, 2^depth, is at least `words`
def depth.go(bits: Nat, +words: Nat, +cap: Nat, +acc: Nat) -> Nat:
  match bits:
    case 0n:
      acc
    case 1n+p:
      depth.step(Nat.is_lt(cap, words), acc,
        _u => depth.go(p, words, Nat.mul(cap, 2n), Nat.add(acc, 1n)))

# the depth of the array that holds this many words, at most 32
def depth(words: Nat) -> Nat:
  depth.go(32n, words, 1n, 0n)

# the string packed into the array, four bytes to a word. A short tail packs
# zeros in the unused bytes; the byte length says they are padding. The walk
# calls itself on the tail, which is the string shrinking.
def fill(text: String, +index: U32, arr: Array<U32>) -> Array<U32>:
  match text:
    case SNil{}:
      arr
    case SCon{w, SNil{}}:
      Array.set(U32, arr, index, pack(byte(w), 0, 0, 0))
    case SCon{w, SCon{x, SNil{}}}:
      Array.set(U32, arr, index, pack(byte(w), byte(x), 0, 0))
    case SCon{w, SCon{x, SCon{y, SNil{}}}}:
      Array.set(U32, arr, index, pack(byte(w), byte(x), byte(y), 0))
    case SCon{w, SCon{x, SCon{y, SCon{z, t}}}}:
      fill(t, U32.inc(index), Array.set(U32, arr, index, pack(byte(w), byte(x), byte(y), byte(z))))

# the string packed into big-endian words, four bytes each
def bytes(+text: String) -> Array<U32>:
  +n = String.length(text)
  fill(text, 0, Array.new(U32, depth(words.of(n)), 0))

# a length that does not fit is not a digest. A digest is sixty-four hex
# characters, so this empty answer cannot be mistaken for one.
def show(answer: Maybe<&1, Array<U32>>) -> String:
  match answer:
    case None{}:
      ""
    case Some{digest}:
      S.hex(digest)

# the hex sha256 digest of a string whose characters are bytes: each one is
# reduced to its low eight bits. NAR serials are held this way.
def raw(+text: String) -> String:
  match text:
    case SNil{}:
      show(S.sha256(bytes(text), 0n))
    case SCon{_c, _t}:
      show(S.sha256(bytes(text), String.length(text)))

# one byte as a character: a UTF-8 string is held in a Bend string one byte to
# a character, the shape `raw` hashes
def utf8.byte(+code: U32) -> Char:
  Chr{(code .&. 255 : U32)}

def utf8.1(+code: U32) -> String:
  SCon{utf8.byte(code), SNil{}}

def utf8.2(+code: U32) -> String:
  SCon{utf8.byte((192 .|. U32.shrn(code, 6n) : U32)),
    SCon{utf8.byte((128 .|. (code .&. 63 : U32) : U32)), SNil{}}}

def utf8.3(+code: U32) -> String:
  SCon{utf8.byte((224 .|. U32.shrn(code, 12n) : U32)),
    SCon{utf8.byte((128 .|. (U32.shrn(code, 6n) .&. 63 : U32) : U32)),
      SCon{utf8.byte((128 .|. (code .&. 63 : U32) : U32)), SNil{}}}}

def utf8.4(+code: U32) -> String:
  SCon{utf8.byte((240 .|. U32.shrn(code, 18n) : U32)),
    SCon{utf8.byte((128 .|. (U32.shrn(code, 12n) .&. 63 : U32) : U32)),
      SCon{utf8.byte((128 .|. (U32.shrn(code, 6n) .&. 63 : U32) : U32)),
        SCon{utf8.byte((128 .|. (code .&. 63 : U32) : U32)), SNil{}}}}}

def utf8.put.3(three: Bool, +code: U32) -> String:
  match three:
    case True{}:
      utf8.3(code)
    case False{}:
      utf8.4(code)

def utf8.put.2(two: Bool, +code: U32) -> String:
  match two:
    case True{}:
      utf8.2(code)
    case False{}:
      utf8.put.3(U32.is_lt(code, 65536), code)

def utf8.put.ascii(ascii: Bool, +code: U32) -> String:
  match ascii:
    case True{}:
      utf8.1(code)
    case False{}:
      utf8.put.2(U32.is_lt(code, 2048), code)

def utf8.put(+code: U32) -> String:
  utf8.put.ascii(U32.is_lt(code, 128), code)

# the string's characters encoded as UTF-8, each byte a character
def utf8(+text: String) -> String:
  match text:
    case SNil{}:
      ""
    case SCon{c, t}:
      utf8.put(Char.to_u32(c)) ++ utf8(t)

# the hex sha256 digest of a text's UTF-8 bytes, which is what `sha256sum`
# says of the file the text was read from, and what `bend --publish` and the
# hub hash a package file and its manifest by. The match is what a symbolic
# string sticks on, so a proof that only unfolds `hash_of` does not enter
# the digest.
def hex(+text: String) -> String:
  match text:
    case SNil{}:
      raw(text)
    case SCon{_c, _t}:
      raw(utf8(text))
