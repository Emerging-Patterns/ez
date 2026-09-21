# http: a GET formatted, and a response taken apart, with no socket in sight
import Base
import ../http.bend as Http
import ../../check/kit.bend as Check

# a response with a Content-Length head
def framed(body: String, len: String) -> String:
  "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: " ++ len
    ++ "\r\n\r\n" ++ body

# a response whose body arrives in chunks
def chunked(body: String) -> String:
  "HTTP/1.1 200 OK\r\nTransfer-Encoding: Chunked\r\n\r\n" ++ body

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a GET names its host and asks for the connection to close",
      Http.request("h.example", "/a.bend"),
      "GET /a.bend HTTP/1.1\r\nHost: h.example\r\nUser-Agent: ez\r\nAccept: */*\r\nConnection: close\r\n\r\n")
    Check.eq_str("a body longer than its Content-Length is cut to it",
      Http.show(Http.parse(framed("hello there", "5"))), "200 hello")
    Check.eq_str("a chunk length counts bytes too",
      Http.show(Http.parse(chunked("6\r\nh\u{e9}llo\r\n0\r\n\r\n"))), "200 h\u{e9}llo")
    Check.eq_str("a status that is not 200 is still read",
      Http.show(Http.parse("HTTP/1.1 404 Not Found\r\nContent-Length: 3\r\n\r\nno!")), "404 no!")
    Check.eq_str("chunks are joined, and the hex length is hex",
      Http.show(Http.parse(chunked("a\r\n0123456789\r\n3\r\nabc\r\n0\r\n\r\n"))),
      "200 0123456789abc")

#|ok a GET names its host and asks for the connection to close
#|ok a body longer than its Content-Length is cut to it
#|ok a chunk length counts bytes too
#|ok a status that is not 200 is still read
#|ok chunks are joined, and the hex length is hex
