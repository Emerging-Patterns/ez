# ez/target: what `ez tool run`, `install` and `upgrade` were asked for,
# decided from the word
# alone. `owner/repo` is GitHub. A URL is that URL. Anything else is a
# path, and a path written `./…`, `../…`, `/…` or `~/…` is a path even
# when it would otherwise read as a repository.
import Base

# where a target names, or why it names nothing
type Place is Data:
  Bad{why: String}
  Local{path: String}
  Remote{url: String, slug: String}

# a char a GitHub owner or repository may hold. A dot is not one: `src/main.bend`
# is a path.
def plain.at(+c: Char) -> Bool:
  Bool.or(Char.is_digit(c), Bool.or(Char.is_alpha(c),
    Bool.or(Char.is_eq(c, '-'), Char.is_eq(c, '_'))))

# one step of a scan that must hold of every char. `Bool.and` reduces both
# sides, so the rest arrives as a thunk.
def plain.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether every char is one a GitHub name may hold
def plain.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      plain.step(plain.at(h), _u => plain.all(t))

# a single path segment of a GitHub shorthand
def seg(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), plain.all(String.to_list(s)))

# the second segment, once the first is in hand. One segment and three are
# not a shorthand.
def two.at(ps: List<&2, String>, +a: String) -> String & String:
  match ps:
    case Nil{}:
      ("", "")
    case Con{+b, Nil{}}:
      (a, b)
    case Con{_b, _t}:
      ("", "")

# the two segments of a shorthand, or two empty strings when it is not one
def two(ps: List<&2, String>) -> String & String:
  match ps:
    case Nil{}:
      ("", "")
    case Con{+a, t}:
      two.at(t, a)

# both segments in hand
def github.go(ab: String & String) -> Bool:
  (a, b) = ab
  Bool.and(seg(a), seg(b))

# `owner/repo`, and not a path that merely contains one slash
def github.ok(+s: String) -> Bool:
  github.go(two(String.split(s, '/')))

# one step of a scan looking for `..`. A slug with one would leave the cache.
def climb.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether any component is a climb
def climb(ps: List<&2, String>) -> Bool:
  match ps:
    case []:
      False{}
    case +h <> t:
      climb.step(String.eq(h, ".."), _u => climb(t))

# a slug that stays under the cache: non-empty, relative, and with no `..`
def slug.ok(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)),
    Bool.and(Bool.not(String.starts_with(s, "/")),
      Bool.not(climb(String.split(s, '/')))))

# a remote whose slug can be a directory, or a refusal when it cannot
def remote(+url: String, +slug: String) -> Place:
  Bool.pick(Place, slug.ok(slug), Remote{url, slug}, Bad{"not a repository"})

# `s` with a suffix of `n` chars taken off when it ends in that suffix.
# `Bool.pick` builds both arms, which is the same trade `pkg/path.unbend` makes.
def cut.end(+s: String, +suf: String, n: Nat) -> String:
  Bool.pick(String, String.ends_with(s, suf),
    String.take(s, Nat.sub(String.length(s), n)), s)

# a trailing slash is not part of the cache directory
def unslash(+s: String) -> String:
  cut.end(s, "/", 1n)

# a trailing `.git` is not part of the cache directory
def ungit(+s: String) -> String:
  cut.end(s, ".git", 4n)

# everything after the first colon. `https://host/path` splits into the
# scheme and `//host/path`.
def body(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case _h <> t:
      String.join(t, ":")

# the `//` a scheme leaves in front of the host
def drop.slashes(+s: String) -> String:
  Bool.pick(String, String.starts_with(s, "//"), String.drop(s, 2n), s)

# `scheme://host/path` as a cache directory
def slug.url(+s: String) -> String:
  ungit(unslash(drop.slashes(body(String.split(s, ':')))))

# `git@host:path` as a cache directory. The colon is the only separator.
def slug.scp(+s: String) -> String:
  ungit(unslash(String.join(String.split(String.drop(s, 4n), ':'), "/")))

# a word that already says it is a path
def looks.path(+s: String) -> Bool:
  Bool.or(String.starts_with(s, "/"),
    Bool.or(String.starts_with(s, "./"),
      Bool.or(String.starts_with(s, "../"),
        String.starts_with(s, "~/"))))

# `owner/repo`, once it is known not to be a URL or a path
def classify.hub(ok: Bool, +s: String) -> Place:
  match ok:
    case True{}:
      remote("https://github.com/" ++ s, "github.com/" ++ s)
    case False{}:
      Local{s}

# a path prefix, or a possible shorthand
def classify.path(local: Bool, +s: String) -> Place:
  match local:
    case True{}:
      Local{s}
    case False{}:
      classify.hub(github.ok(s), s)

# `git@host:path`, or a path
def classify.scp(scp: Bool, +s: String) -> Place:
  match scp:
    case True{}:
      remote(s, slug.scp(s))
    case False{}:
      classify.path(looks.path(s), s)

# a URL, or not
def classify.url(url: Bool, +s: String) -> Place:
  match url:
    case True{}:
      remote(s, slug.url(s))
    case False{}:
      classify.scp(String.starts_with(s, "git@"), s)

# nothing was asked for
def classify.empty(empty: Bool, +s: String) -> Place:
  match empty:
    case True{}:
      Bad{"a target is needed"}
    case False{}:
      classify.url(String.contains(s, "://"), s)

# what a target word names
def classify(+s: String) -> Place:
  classify.empty(String.is_empty(s), s)

# `~` and `~/…` expanded. Anything else is already a path.
def expand(+home: String, +path: String) -> String:
  Bool.pick(String, String.eq(path, "~"), home,
    Bool.pick(String, String.starts_with(path, "~/"),
      home ++ String.drop(path, 1n), path))

# the entry, or `main.bend` when a ledger names none
def entry.or(+e: String) -> String:
  Bool.pick(String, String.is_empty(e), "main.bend", e)

# the file that is built: `bin` when the ledger names one, otherwise the entry
def file.of(+bin: String, +entry: String) -> String:
  Bool.pick(String, String.is_empty(bin), entry.or(entry), bin)

# the binary's name: the package's, or `app` when the ledger names none
def out.name(+n: String) -> String:
  Bool.pick(String, String.is_empty(n), "app", n)

# a place on one line, for a proof to read
def show(p: Place) -> String:
  match p:
    case Bad{why}:
      "bad " ++ why
    case Local{path}:
      "local " ++ path
    case Remote{url, slug}:
      "remote " ++ url ++ " " ++ slug
