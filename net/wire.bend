# net/wire: the foreign effect under the client. One request out and one
# response back, over a socket this effect opens and closes itself.
#
# It is not Base's TCP. Base has sockets, but `TCP.connect` puts its host
# through `inet_pton`, so it reaches an address literal and no name; and Base
# has no crypto at all, while `bend -o` links with exactly
# `-std=c11 -O3 -lpthread -lm`, so -lssl can never join it. Both twins
# therefore resolve the name themselves and open OpenSSL at run time with
# dlopen, where a link line has no say.
import Base

# the exchange: a spec in, and the status on its own first line then the raw
# response, the same answer shape run/run.bend uses
def ezwire.talk(spec: String) -> IO(String):
  import "./effs/wire.c"
  import "./effs/wire.js"

# the word the effect reads for a scheme that wants TLS
def scheme(secure: Bool) -> String:
  match secure:
    case True{}:
      "tls"
    case False{}:
      "tcp"

# the spec the effect reads: the scheme, the host and the port on lines of
# their own, and everything after the third newline is the request verbatim
def spec(secure: Bool, host: String, port: U32, req: String) -> String:
  scheme(secure) ++ "\n" ++ host ++ "\n" ++ U32.show(port) ++ "\n" ++ req

# a request sent to a host and its whole answer read back
def talk(secure: Bool, host: String, port: U32, req: String) -> IO(String):
  ezwire.talk(spec(secure, host, port, req))
