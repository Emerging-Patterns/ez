# A whole file is read or written in one call. Base gives an open handle and
# chunked reads; this package is the loop over them, so what is stated here
# is that shape: a write's bytes come back as the same text, and a path that
# would not open is nothing.
import Base
import ../src/io/file.bend as FFile

# LAW: the text of a file that was read is the bytes that were there. The
# same text written and then read is this Some, and this Some is those bytes.
law write_read:
  for +s: String
  {FFile.text_of(Some{s}) == s : String}
