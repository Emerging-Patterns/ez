# The plaintext HTTP ez's test servers speak (src/check/serve.bend), which
# check/framing.bend and check/oracle.bend answer through. This is internal:
# the test servers are not part of ez, and these laws hold their reading and
# framing in place so a test fails on ez and not on its own server.
#
# A request's head ends at its first blank line, a line that is empty or is a
# lone `\r`; the head lines before it are kept in order, and the body is
# everything after it, joined back with the newlines it was split on. A head
# that came out empty has not arrived. The body's length is the head's
# Content-Length, read from the first line that starts with it, whatever its
# case; a head with none says zero. An answer states its body's length in the
# bytes it goes over the wire as, an ASCII character being one byte, and says
# the connection closes. A list of words is indexed from zero, and an index
# past the end is "".
import Base
import ../src/check/serve.bend as S

# LAW: an ASCII character takes one byte on the wire
law width_ascii:
  for +code: U32
  for e: {True{} == U32.is_lt(code, 128) : Bool}
  {S.width(code) == 1 : U32}

# LAW: so a string headed by an ASCII character is one byte longer than its tail
law size_ascii:
  for +ch: Char
  for tail: String
  for e: {True{} == U32.is_lt(Char.to_u32(ch), 128) : Bool}
  {S.size(SCon{ch, tail}) == U32.add(1, S.size(tail)) : U32}

# LAW: the word at index zero is the first
law at_first:
  for word: String
  for rest: List<&2, String>
  {S.at(word <> rest, 0n) == word : String}

# LAW: the word at the next index is the one at that index of the rest
law at_next:
  for word: String
  for rest: List<&2, String>
  for index: Nat
  {S.at(word <> rest, 1n+index) == S.at(rest, index) : String}

# LAW: an index past the end of the words is ""
law at_past:
  for index: Nat
  {S.at([], index) == "" : String}

# LAW: an empty line ends the head, and the lines after it are the body
law cut_blank:
  for lines: List<&2, String>
  {S.cut("" <> lines) == S.MFull{[], String.join(lines, "\n")} : S.Msg}

# LAW: and so does a lone `\r`, which is how a CRLF blank line splits
law cut_cr:
  for lines: List<&2, String>
  {S.cut("\r" <> lines) == S.MFull{[], String.join(lines, "\n")} : S.Msg}

# LAW: any other line is a head line, kept in front of the head the rest gives
law cut_line:
  for +line: String
  for lines: List<&2, String>
  for e: {False{} == Bool.or(String.is_empty(line), String.eq(line, "\r")) : Bool}
  {S.cut(line <> lines) == S.cut.put(line, S.cut(lines)) : S.Msg}

# LAW: a head that came out empty is a request that has not arrived
law empty_head_partial:
  for body: String
  {S.msg.at(S.MFull{[], body}) == S.MPartial{} : S.Msg}

# LAW: a head line that does not state the Content-Length is passed over
law clen_skip:
  for +line: String
  for lines: List<&2, String>
  for e: {False{} == String.starts_with(String.to_lower(line), "content-length:") : Bool}
  {S.clen(line <> lines) == S.clen(lines) : U32}

# LAW: the first one that does gives the length it states, zero when it states
# no number
law clen_read:
  for +line: String
  for lines: List<&2, String>
  for e: {True{} == String.starts_with(String.to_lower(line), "content-length:") : Bool}
  {S.clen(line <> lines)
    == Maybe.default(&2, U32, U32.read(String.trim(String.drop(line, 15n))), 0) : U32}

# LAW: an answer is its status, its body's length in bytes, the close, and the
# body
law response_frames:
  for status: String
  for +body: String
  {S.response(status, body)
    == "HTTP/1.1 " ++ status ++ "\r\nContent-Length: " ++ U32.show(S.size(body)) ++
      "\r\nConnection: close\r\n\r\n" ++ body : String}
