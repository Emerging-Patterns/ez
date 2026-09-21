# io: the laws. The human states them; PROOF.bend must prove them. A whole
# file is read or written in one call. Base gives an open handle and chunked
# reads; this package is the loop over them, so what is stated here is that
# shape: a write's bytes come back as the same text, and a path that would
# not open is nothing, which is the empty string.
import Base
import ./file.bend as F

# LAW: a write that reported success is success. The handle is shut and the
# result is this bit, so a file that was written answers True.
law write_ok:
  {F.write.ok(Done{Unit{}}) == True{} : Bool}

# LAW: the text of a file that was read is the bytes that were there. The
# same text written and then read is this Some, and this Some is those bytes.
law write_read:
  for +s: String
  {F.text_of(Some{s}) == s : String}

# LAW: a file that would not open is nothing. The miss is None, not an empty
# body, so a path that is not there is told apart from a file that holds "".
law read_miss:
  for e: U32 & String
  {F.read.opened(Fail{e}) == IO.pure(Maybe<&2, String>, None{})
    : IO(Maybe<&2, String>)}

# LAW: and the text of nothing is the empty string. The rest of ez reads a
# file as `text_of` of what `read` answered, so a missing path is "".
law text_of_none:
  {F.text_of(None{}) == "" : String}
