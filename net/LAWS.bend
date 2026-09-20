# net: the laws. The human states them; PROOF.bend must prove them. A body
# framed by a byte count is the one place in ez where a miscount is silent:
# the bytes still decode, they are just the wrong bytes. So the framing is
# proved rather than sampled.
import Base
import ./http.bend as Http

# LAW: take and drop partition a string at the same byte offset, whatever the
# offset and whatever the string holds. Nothing is lost between them and
# nothing is counted twice.
law utf8_split:
  for s: String
  for +n: Nat
  {String.append(Http.utf8.take(s, n), Http.utf8.drop(s, n)) == s : String}

# LAW: a body whose Content-Length is its own byte count comes back exactly,
# with nothing cut off its end and nothing left on it. This is the claim the
# whole client rests on: a framed body is the body.
law clen_exact:
  for st: U32
  for +body: String
  {Http.parse.clen(st, Http.utf8.len(body), body) == Http.Reply{st, body} : Http.Reply}
