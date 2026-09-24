# ez/target: what `ez add`, `ez tool run`, `install` and `upgrade` were asked
# for, decided from the word alone. `owner/repo` is GitHub. A URL is that URL.
# Anything else is a path, and a path written `./…`, `../…`, `/…` or `~/…` is
# a path even when it would otherwise read as a repository. For `ez add`, a
# word bend reads as a hub package's `<name>@<version>` names that package,
# where it would otherwise be a path (`aim`).
import Base
import ../pkg/pkg.bend as K

# where a target names, or why it names nothing
type Place is Data:
  Bad{why: String}
  Local{path: String}
  Remote{url: String, slug: String}

# a char a GitHub owner or repository may hold besides a dot: a letter, a
# digit, `-` or `_`
def plain.at(+ch: Char) -> Bool:
  Bool.or(Char.is_digit(ch), Bool.or(Char.is_alpha(ch),
    Bool.or(Char.is_eq(ch, '-'), Char.is_eq(ch, '_'))))

# what one char of a target is, as far as telling a shorthand from a path
# goes. A colon is asked about first, so a char that is anything but `Other`
# is known not to be one: that is what lets a proof say a shorthand never
# contains `://`.
type Mark is Data:
  Slash{}
  Dot{}
  Tilde{}
  Word{}
  Other{}

def kind.word(word: Bool) -> Mark:
  match word:
    case True{}:
      Word{}
    case False{}:
      Other{}

def kind.tilde(tilde: Bool, word: Bool) -> Mark:
  match tilde:
    case True{}:
      Tilde{}
    case False{}:
      kind.word(word)

def kind.dot(dot: Bool, tilde: Bool, word: Bool) -> Mark:
  match dot:
    case True{}:
      Dot{}
    case False{}:
      kind.tilde(tilde, word)

def kind.slash(slash: Bool, dot: Bool, tilde: Bool, word: Bool) -> Mark:
  match slash:
    case True{}:
      Slash{}
    case False{}:
      kind.dot(dot, tilde, word)

def kind.colon(colon: Bool, slash: Bool, dot: Bool, tilde: Bool, word: Bool) -> Mark:
  match colon:
    case True{}:
      Other{}
    case False{}:
      kind.slash(slash, dot, tilde, word)

# a char's kind
def kind(+ch: Char) -> Mark:
  kind.colon(Char.is_eq(ch, ':'), Char.is_eq(ch, '/'), Char.is_eq(ch, '.'),
    Char.is_eq(ch, '~'), plain.at(ch))

# one char of a name, with the rest of the name still to be asked about.
# The rest arrives as a thunk, so a char that ends the name ends the walk.
def name.keep(mark: Mark, rest: Unit -> Bool) -> Bool:
  match mark:
    case Word{}:
      rest(Unit{})
    case Dot{}:
      rest(Unit{})
    case Slash{}:
      False{}
    case Tilde{}:
      False{}
    case Other{}:
      False{}

# every char a letter, a digit, `-`, `_` or `.`
def name.all(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      name.keep(kind(h), _u => name.all(t))

# after `..`: one more name char, so the segment is not `..`
def seg.dots(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      name.keep(kind(h), _u => name.all(t))

# the second char after a leading dot
def seg.dot2(mark: Mark, rest: String) -> Bool:
  match mark:
    case Word{}:
      name.all(rest)
    case Dot{}:
      seg.dots(rest)
    case Slash{}:
      False{}
    case Tilde{}:
      False{}
    case Other{}:
      False{}

# after a leading `.`: more, so the segment is not `.`
def seg.dot(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      seg.dot2(kind(h), t)

# the first char of a segment
def seg.first(mark: Mark, rest: String) -> Bool:
  match mark:
    case Word{}:
      name.all(rest)
    case Dot{}:
      seg.dot(rest)
    case Slash{}:
      False{}
    case Tilde{}:
      False{}
    case Other{}:
      False{}

# one segment of a GitHub shorthand: letters, digits, `-`, `_` and `.`, at
# least one of them, and not `.` or `..`, which name a directory
def seg(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      seg.first(kind(h), t)

# a word cut at its first slash, or not cut because a char before any slash
# could not be in a shorthand
type Halves is Data:
  Uncut{}
  Two{left: String, right: String}

# a char put back in front of the left half
def halve.put(ch: Char, halves: Halves) -> Halves:
  match halves:
    case Uncut{}:
      Uncut{}
    case Two{left, right}:
      Two{SCon{ch, left}, right}

# one char of the first segment. A slash ends it; the rest of the word is
# asked about only past a char a segment may hold.
def halve.at(mark: Mark, ch: Char, +tail: String, rest: Unit -> Halves) -> Halves:
  match mark:
    case Slash{}:
      Two{"", tail}
    case Word{}:
      halve.put(ch, rest(Unit{}))
    case Dot{}:
      halve.put(ch, rest(Unit{}))
    case Tilde{}:
      Uncut{}
    case Other{}:
      Uncut{}

# the word before its first slash and the word after it
def halve(text: String) -> Halves:
  match text:
    case SNil{}:
      Uncut{}
    case SCon{+h, +t}:
      halve.at(kind(h), h, t, _u => halve(t))

# a word naming a Bend file. As the second of two segments it is the last
# component of a path, `src/main.bend`, and not a repository.
def bend.file(+text: String) -> Bool:
  String.ends_with(text, ".bend")

# the second segment of a shorthand: a segment that is not a Bend file
def repo.seg(+text: String) -> Bool:
  Bool.and(seg(text), Bool.not(bend.file(text)))

# both segments of a shorthand, where there are two
def github.halves(halves: Halves) -> Bool:
  match halves:
    case Uncut{}:
      False{}
    case Two{left, right}:
      Bool.and(seg(left), repo.seg(right))

# `owner/repo`: exactly two segments, each a `seg`, the second not ending in
# `.bend`. A second slash leaves the right half with a slash in it, which no
# segment holds.
def github.ok(text: String) -> Bool:
  github.halves(halve(text))

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

# a URL with no host, `file:///srv/repo`, is on this host, and is cached
# where `file://localhost/srv/repo` is, rather than at an absolute slug
def hostless(+text: String) -> String:
  Bool.pick(String, String.starts_with(text, "/"), "localhost" ++ text, text)

# `scheme://host/path` as a cache directory
def slug.url(+text: String) -> String:
  ungit(unslash(hostless(drop.slashes(body(String.split(text, ':'))))))

# `git@host:path` as a cache directory. The colon is the only separator.
def slug.scp(+text: String) -> String:
  ungit(unslash(String.join(String.split(String.drop(text, 4n), ':'), "/")))

# the char after `~` or `..`: a slash
def looks.slash.at(mark: Mark) -> Bool:
  match mark:
    case Slash{}:
      True{}
    case Dot{}:
      False{}
    case Tilde{}:
      False{}
    case Word{}:
      False{}
    case Other{}:
      False{}

def looks.slash(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, _t}:
      looks.slash.at(kind(h))

# the char after a leading dot: `./` or `../`
def looks.dot.at(mark: Mark, rest: String) -> Bool:
  match mark:
    case Slash{}:
      True{}
    case Dot{}:
      looks.slash(rest)
    case Tilde{}:
      False{}
    case Word{}:
      False{}
    case Other{}:
      False{}

def looks.dot(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      looks.dot.at(kind(h), t)

# the first char: `/`, or the start of `./`, `../` or `~/`
def looks.first(mark: Mark, rest: String) -> Bool:
  match mark:
    case Slash{}:
      True{}
    case Dot{}:
      looks.dot(rest)
    case Tilde{}:
      looks.slash(rest)
    case Word{}:
      False{}
    case Other{}:
      False{}

# a word that already says it is a path: it starts `/`, `./`, `../` or `~/`
def looks.path(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      looks.first(kind(h), t)

# `git@host:path`, or a path
def classify.scp(scp: Bool, +text: String) -> Place:
  match scp:
    case True{}:
      remote(text, slug.scp(text))
    case False{}:
      Local{text}

# `owner/repo`. Its slug is safe without the check a URL's gets: neither
# segment is empty, `.`, `..` or holds a slash, so it cannot climb out of the
# cache. A trailing `.git` is not part of the cache directory, as for a URL.
def classify.hub(ok: Bool, +text: String) -> Place:
  match ok:
    case True{}:
      Remote{"https://github.com/" ++ text, "github.com/" ++ ungit(text)}
    case False{}:
      classify.scp(String.starts_with(text, "git@"), text)

# a path prefix, or a possible shorthand
def classify.path(local: Bool, +text: String) -> Place:
  match local:
    case True{}:
      Local{text}
    case False{}:
      classify.hub(github.ok(text), text)

# a URL, or not
def classify.url(url: Bool, +text: String) -> Place:
  match url:
    case True{}:
      remote(text, slug.url(text))
    case False{}:
      classify.path(looks.path(text), text)

# nothing was asked for
def classify.empty(empty: Bool, +text: String) -> Place:
  match empty:
    case True{}:
      Bad{"a target is needed"}
    case False{}:
      classify.url(String.contains(text, "://"), text)

# what a target word names. A word with `://` in it is a URL; one starting
# `/`, `./`, `../` or `~/` is a path; `owner/repo` is GitHub; one starting
# `git@` is a URL; anything else is a path. The shorthand is asked about
# before `git@` because no shorthand holds an `@`, and in that order the
# shorthand's law needs nothing said about `git@`.
def classify(+text: String) -> Place:
  classify.empty(String.is_empty(text), text)

# what `ez add` was asked for: a hub package by its `<name>@<version>`, or a
# place as `classify` reads it
type Aim is Data:
  Named{nv: String}
  Placed{place: Place}

# a word `classify` reads as a path names a hub package when bend's NAMED rule
# rules it in (`K.name.ok`); otherwise it is that path
def aim.local(named: Bool, +text: String, +path: String) -> Aim:
  match named:
    case True{}:
      Named{text}
    case False{}:
      Placed{Local{path}}

# the place read, with only a path asked whether it is a name. A URL, a
# `git@host:path` and an `owner/repo` are never read again, so nothing that
# was a remote becomes a name.
def aim.place(place: Place, +text: String) -> Aim:
  match place:
    case Bad{why}:
      Placed{Bad{why}}
    case Local{path}:
      aim.local(K.name.ok(text), text, path)
    case Remote{url, slug}:
      Placed{Remote{url, slug}}

# what an `ez add` target names. A name holds no `/` and no `:`, and starts
# with a letter, so a word bend reads as a name is one `classify` reads as a
# path, and only such a word is asked.
def aim(+text: String) -> Aim:
  aim.place(classify(text), text)

# whether a target names a hub package
def aim.named(aim: Aim) -> Bool:
  match aim:
    case Named{_nv}:
      True{}
    case Placed{_place}:
      False{}

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
