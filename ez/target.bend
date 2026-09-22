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
def plain.at(+ch: Char) -> Bool:
  Bool.or(Char.is_digit(ch), Bool.or(Char.is_alpha(ch),
    Bool.or(Char.is_eq(ch, '-'), Char.is_eq(ch, '_'))))

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
def seg(+text: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(text)), plain.all(String.to_list(text)))

# the second segment, once the first is in hand. One segment and three are
# not a shorthand.
def two.at(ps: List<&2, String>, +first: String) -> String & String:
  match ps:
    case Nil{}:
      ("", "")
    case Con{+b, Nil{}}:
      (first, b)
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
def github.ok(+text: String) -> Bool:
  github.go(two(String.split(text, '/')))

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
def slug.ok(+text: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(text)),
    Bool.and(Bool.not(String.starts_with(text, "/")),
      Bool.not(climb(String.split(text, '/')))))

# a remote whose slug can be a directory, or a refusal when it cannot
def remote(+url: String, +slug: String) -> Place:
  Bool.pick(Place, slug.ok(slug), Remote{url, slug}, Bad{"not a repository"})

# `s` with a suffix of `n` chars taken off when it ends in that suffix.
# `Bool.pick` builds both arms, which is the same trade `pkg/path.unbend` makes.
def cut.end(+text: String, +suf: String, len: Nat) -> String:
  Bool.pick(String, String.ends_with(text, suf),
    String.take(text, Nat.sub(String.length(text), len)), text)

# a trailing slash is not part of the cache directory
def unslash(+text: String) -> String:
  cut.end(text, "/", 1n)

# a trailing `.git` is not part of the cache directory
def ungit(+text: String) -> String:
  cut.end(text, ".git", 4n)

# everything after the first colon. `https://host/path` splits into the
# scheme and `//host/path`.
def body(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case _h <> t:
      String.join(t, ":")

# the `//` a scheme leaves in front of the host
def drop.slashes(+text: String) -> String:
  Bool.pick(String, String.starts_with(text, "//"), String.drop(text, 2n), text)

# `scheme://host/path` as a cache directory
def slug.url(+text: String) -> String:
  ungit(unslash(drop.slashes(body(String.split(text, ':')))))

# `git@host:path` as a cache directory. The colon is the only separator.
def slug.scp(+text: String) -> String:
  ungit(unslash(String.join(String.split(String.drop(text, 4n), ':'), "/")))

# a word that already says it is a path
def looks.path(+text: String) -> Bool:
  Bool.or(String.starts_with(text, "/"),
    Bool.or(String.starts_with(text, "./"),
      Bool.or(String.starts_with(text, "../"),
        String.starts_with(text, "~/"))))

# `owner/repo`, once it is known not to be a URL or a path
def classify.hub(ok: Bool, +text: String) -> Place:
  match ok:
    case True{}:
      remote("https://github.com/" ++ text, "github.com/" ++ text)
    case False{}:
      Local{text}

# a path prefix, or a possible shorthand
def classify.path(local: Bool, +text: String) -> Place:
  match local:
    case True{}:
      Local{text}
    case False{}:
      classify.hub(github.ok(text), text)

# `git@host:path`, or a path
def classify.scp(scp: Bool, +text: String) -> Place:
  match scp:
    case True{}:
      remote(text, slug.scp(text))
    case False{}:
      classify.path(looks.path(text), text)

# a URL, or not
def classify.url(url: Bool, +text: String) -> Place:
  match url:
    case True{}:
      remote(text, slug.url(text))
    case False{}:
      classify.scp(String.starts_with(text, "git@"), text)

# nothing was asked for
def classify.empty(empty: Bool, +text: String) -> Place:
  match empty:
    case True{}:
      Bad{"a target is needed"}
    case False{}:
      classify.url(String.contains(text, "://"), text)

# what a target word names
def classify(+text: String) -> Place:
  classify.empty(String.is_empty(text), text)

# `~` and `~/…` expanded. Anything else is already a path.
def expand(+home: String, +path: String) -> String:
  Bool.pick(String, String.eq(path, "~"), home,
    Bool.pick(String, String.starts_with(path, "~/"),
      home ++ String.drop(path, 1n), path))

# the entry, or `main.bend` when a ledger names none
def entry.or(+path: String) -> String:
  Bool.pick(String, String.is_empty(path), "main.bend", path)

# the file that is built: `bin` when the ledger names one, otherwise the entry
def file.of(+bin: String, +entry: String) -> String:
  Bool.pick(String, String.is_empty(bin), entry.or(entry), bin)

# the binary's name: the package's, or `app` when the ledger names none
def out.name(+name: String) -> String:
  Bool.pick(String, String.is_empty(name), "app", name)

# a place on one line, for a proof to read
def show(place: Place) -> String:
  match place:
    case Bad{why}:
      "bad " ++ why
    case Local{path}:
      "local " ++ path
    case Remote{url, slug}:
      "remote " ++ url ++ " " ++ slug
