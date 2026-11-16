# What the framing test server (src/check/framing.bend) answers, which is what
# tests/fetch.bend drives ezhttp's client against. This is internal: the
# server is a test fixture, not part of ez, and these laws hold its routes in
# place so a failing fetch test is about the client.
#
# Exactly four answers, by the request's path: `/plain` is the plain body
# framed by its length, `/chunked` is the chunked body framed in chunks, `/`
# is `ok` so a test can wait on the server, and any other path is a 404 with
# no body. A chunk states its length in lower-case hex, one digit below 16.
# also rests on: laws/ServeSpeaksHttp.bend
import Base
import ../src/check/serve.bend as S
import ../src/check/framing.bend as F

# LAW: `/plain` is the plain body, framed by its length
law reply_plain:
  for +path: String
  for is_plain: {True{} == String.eq(path, "/plain") : Bool}
  {F.reply(path) == S.response("200 OK", F.plain()) : String}

# LAW: `/chunked` is the chunked body
law reply_chunked:
  for +path: String
  for not_plain: {False{} == String.eq(path, "/plain") : Bool}
  for is_chunked: {True{} == String.eq(path, "/chunked") : Bool}
  {F.reply(path) == F.chunked() : String}

# LAW: `/` is `ok`
law reply_root:
  for +path: String
  for not_plain: {False{} == String.eq(path, "/plain") : Bool}
  for not_chunked: {False{} == String.eq(path, "/chunked") : Bool}
  for is_root: {True{} == String.eq(path, "/") : Bool}
  {F.reply(path) == S.response("200 OK", "ok") : String}

# LAW: and every other path is a 404 with no body
law reply_unknown:
  for +path: String
  for not_plain: {False{} == String.eq(path, "/plain") : Bool}
  for not_chunked: {False{} == String.eq(path, "/chunked") : Bool}
  for not_root: {False{} == String.eq(path, "/") : Bool}
  {F.reply(path) == S.response("404 Not Found", "") : String}

# LAW: a chunk is its length in hex, its bytes, each ended by a CRLF
law chunk_frames:
  for +text: String
  {F.chunk(text) == F.hex.show(S.size(text)) ++ "\r\n" ++ text ++ "\r\n" : String}

# LAW: a length below 16 is one hex digit
law hex_one_digit:
  for +len: U32
  for small: {True{} == U32.is_lt(len, 16) : Bool}
  {F.hex.show(len) == F.hex.digit(len) : String}

# LAW: a longer one is its sixteens and then its ones
law hex_two_digits:
  for +len: U32
  for big: {False{} == U32.is_lt(len, 16) : Bool}
  {F.hex.show(len) == F.hex.digit(U32.div(len, 16)) ++ F.hex.digit(U32.mod(len, 16)) : String}
