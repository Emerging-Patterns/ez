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
    Check.eq_str("a Content-Length body is the status and that many chars",
      Http.show(Http.parse(framed("hello", "5"))), "200 hello")
    Check.eq_str("a body longer than its Content-Length is cut to it",
      Http.show(Http.parse(framed("hello there", "5"))), "200 hello")
    Check.eq_str("a body shorter than its Content-Length is a torn response",
      Http.show(Http.parse(framed("hel", "5"))),
      "torn the response body stopped before its Content-Length")
    Check.eq_str("a chunk length counts bytes too",
      Http.show(Http.parse(chunked("6\r\nh\u{e9}llo\r\n0\r\n\r\n"))), "200 h\u{e9}llo")
    Check.eq_str("with no framing header the whole rest is the body",
      Http.show(Http.parse("HTTP/1.1 200 OK\r\n\r\nplain")), "200 plain")
    Check.eq_str("a status that is not 200 is still read",
      Http.show(Http.parse("HTTP/1.1 404 Not Found\r\nContent-Length: 3\r\n\r\nno!")), "404 no!")
    Check.eq_str("a header is found whatever case it was written in",
      Http.show(Http.parse(chunked("5\r\nhello\r\n0\r\n\r\n"))), "200 hello")
    Check.eq_str("chunks are joined, and the hex length is hex",
      Http.show(Http.parse(chunked("a\r\n0123456789\r\n3\r\nabc\r\n0\r\n\r\n"))),
      "200 0123456789abc")
    Check.eq_str("a chunk extension does not change the length",
      Http.show(Http.parse(chunked("3;name=v\r\nabc\r\n0\r\n\r\n"))), "200 abc")
    Check.eq_str("a chunked body decodes the same however the reads fell",
      Http.dechunk("2\r\nab\r\n2\r\ncd\r\n0\r\n\r\n"),
      Http.dechunk("2\r\nab\r\n" ++ "2\r\n" ++ "cd\r\n0\r\n\r\n"))
    Check.eq_str("bytes that are not a response are torn, not an empty body",
      Http.show(Http.parse("<html>nope</html>")),
      "torn the response head has no blank line after it")
    Check.eq_str("a head with no status line is torn",
      Http.show(Http.parse("garbage\r\n\r\nbody")), "torn the response has no status line")

#|ok a GET names its host and asks for the connection to close
#|ok a Content-Length body is the status and that many chars
#|ok a body longer than its Content-Length is cut to it
#|ok a body shorter than its Content-Length is a torn response
#|ok a chunk length counts bytes too
#|ok with no framing header the whole rest is the body
#|ok a status that is not 200 is still read
#|ok a header is found whatever case it was written in
#|ok chunks are joined, and the hex length is hex
#|ok a chunk extension does not change the length
#|ok a chunked body decodes the same however the reads fell
#|ok bytes that are not a response are torn, not an empty body
#|ok a head with no status line is torn
