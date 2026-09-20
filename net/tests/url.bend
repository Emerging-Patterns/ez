# url: a url comes apart into the four things a GET needs
import Base
import ../url.bend as Url
import ../../check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("https implies 443 and / implies the root",
      Url.show(Url.parse("https://hub.bend-lang.com")), "https hub.bend-lang.com 443 /")
    Check.eq_str("http implies 80",
      Url.show(Url.parse("http://example.org/a/b.bend")), "http example.org 80 /a/b.bend")
    Check.eq_str("a port named is the port used",
      Url.show(Url.parse("http://127.0.0.1:8080/x")), "http 127.0.0.1 8080 /x")
    Check.eq_str("a trailing slash is the root",
      Url.show(Url.parse("http://h/")), "http h 80 /")
    Check.eq_str("the scheme is read without case",
      Url.show(Url.parse("HTTPS://h/x")), "https h 443 /x")
    Check.eq_str("a file url has no host and keeps its absolute path",
      Url.show(Url.parse("file:///tmp/x/manifest")), "file  80 /tmp/x/manifest")
    Check.eq_str("a colon in the path is not the scheme's",
      Url.show(Url.parse("http://h/a:b")), "http h 80 /a:b")
    Check.eq_str("a url with no // is refused",
      Url.show(Url.parse("https:hub")), "bad https:hub has no //")

#|ok https implies 443 and / implies the root
#|ok http implies 80
#|ok a port named is the port used
#|ok a trailing slash is the root
#|ok the scheme is read without case
#|ok a file url has no host and keeps its absolute path
#|ok a colon in the path is not the scheme's
#|ok a url with no // is refused
