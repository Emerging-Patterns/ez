# A target containing `://` or starting `git@` is a git URL. A target starting
# `/`, `./`, `../` or `~/` is a path. A target of exactly two segments of
# letters, digits, `-`, `_` and `.`, neither of them `.` or `..`, is
# `https://github.com/<target>`, unless its second segment ends in `.bend`,
# which makes it a path. Anything else is a path, except the empty word, which
# is refused. For `ez add`, a path bend reads as a hub package's
# `<name>@<version>` names that package on the hub; a git URL, `owner/repo` or
# other path never does.
import Base
import ../src/pkg/pkg.bend as K
import ../src/ez/target.bend as Tgt

# target: what a word names. The four ways a word can name something are
# each a law over every word of that shape, and together they are
# laws/TargetClassified.bend.

# LAW: a target with `://` in it is a git URL, whatever is around it
law classify_url:
  for +a: String
  for +b: String
  {Tgt.classify(a ++ ("://" ++ b))
    == Tgt.remote(a ++ ("://" ++ b), Tgt.slug.url(a ++ ("://" ++ b)))
    : Tgt.Place}

# LAW: a target starting `git@` is a git URL
law classify_scp:
  for +rest: String
  for e: {False{} == String.contains("git@" ++ rest, "://") : Bool}
  {Tgt.classify("git@" ++ rest)
    == Tgt.remote("git@" ++ rest, Tgt.slug.scp("git@" ++ rest)) : Tgt.Place}

# LAW: a target starting `/` is a path
law classify_abs:
  for +rest: String
  for e: {False{} == String.contains("/" ++ rest, "://") : Bool}
  {Tgt.classify("/" ++ rest) == Tgt.Local{"/" ++ rest} : Tgt.Place}

# LAW: a target starting `./` is a path, even when what follows is
# `owner/repo`
law classify_here:
  for +rest: String
  for e: {False{} == String.contains("./" ++ rest, "://") : Bool}
  {Tgt.classify("./" ++ rest) == Tgt.Local{"./" ++ rest} : Tgt.Place}

# LAW: a target starting `../` is a path
law classify_up:
  for +rest: String
  for e: {False{} == String.contains("../" ++ rest, "://") : Bool}
  {Tgt.classify("../" ++ rest) == Tgt.Local{"../" ++ rest} : Tgt.Place}

# LAW: a target starting `~/` is a path
law classify_home:
  for +rest: String
  for e: {False{} == String.contains("~/" ++ rest, "://") : Bool}
  {Tgt.classify("~/" ++ rest) == Tgt.Local{"~/" ++ rest} : Tgt.Place}

# LAW: two segments of letters, digits, `-`, `_` and `.`, neither of them `.`
# or `..`, and the second not ending in `.bend`, are that repository on
# GitHub. `vercel/next.js` is one, and so is `o/r.git`, which is cached without
# its `.git` as its URL would be. `src/main.bend` is not.
law classify_github:
  for +a: String
  for +b: String
  for ea: {Tgt.seg(a) == True{} : Bool}
  for eb: {Tgt.seg(b) == True{} : Bool}
  for ef: {Tgt.bend.file(b) == False{} : Bool}
  {Tgt.classify(a ++ ("/" ++ b))
    == Tgt.Remote{"https://github.com/" ++ (a ++ ("/" ++ b)),
      "github.com/" ++ Tgt.ungit(a ++ ("/" ++ b))} : Tgt.Place}

# LAW: anything else is a path: a word with no `://`, not starting `git@`,
# `/`, `./`, `../` or `~/`, and not two such segments around a slash with
# the second not ending in `.bend`. The
# empty word is not a target at all, and is refused.
law classify_else:
  for +text: String
  for ne: {False{} == String.is_empty(text) : Bool}
  for eu: {False{} == String.contains(text, "://") : Bool}
  for eg: {False{} == String.starts_with(text, "git@") : Bool}
  for e1: {False{} == String.starts_with(text, "/") : Bool}
  for e2: {False{} == String.starts_with(text, "./") : Bool}
  for e3: {False{} == String.starts_with(text, "../") : Bool}
  for e4: {False{} == String.starts_with(text, "~/") : Bool}
  for no: @a:String -> @b:String -> {text == a ++ ("/" ++ b) : String}
    -> {Tgt.seg(a) == True{} : Bool} -> {Tgt.seg(b) == True{} : Bool}
    -> {Tgt.bend.file(b) == False{} : Bool} -> Empty
  {Tgt.classify(text) == Tgt.Local{text} : Tgt.Place}

# ---------------------------------------------------------------------------
# a hub package's `<name>@<version>` as an `ez add` target (`Tgt.aim`)

# LAW: a word `classify` reads as a path is a hub package's name when bend's
# NAMED rule rules it in. Every such name reads as a path: it holds no `/`
# and no `:`, and its name part runs to 12 characters before its `@`, so it
# never starts `git@`.
law aim_named:
  for +text: String
  for +p: String
  for e: {Tgt.classify(text) == Tgt.Local{p} : Tgt.Place}
  for n: {K.name.ok(text) == True{} : Bool}
  {Tgt.aim(text) == Tgt.Named{text} : Tgt.Aim}

# LAW: and any other path stays that path
law aim_path:
  for +text: String
  for +p: String
  for e: {Tgt.classify(text) == Tgt.Local{p} : Tgt.Place}
  for n: {K.name.ok(text) == False{} : Bool}
  {Tgt.aim(text) == Tgt.Placed{Tgt.Local{p}} : Tgt.Aim}

# LAW: a git URL or an `owner/repo` is never read as a name
law aim_remote:
  for +text: String
  for +url: String
  for +slug: String
  for e: {Tgt.classify(text) == Tgt.Remote{url, slug} : Tgt.Place}
  {Tgt.aim(text) == Tgt.Placed{Tgt.Remote{url, slug}} : Tgt.Aim}

# LAW: nor is a word that names nothing
law aim_bad:
  for +text: String
  for +why: String
  for e: {Tgt.classify(text) == Tgt.Bad{why} : Tgt.Place}
  {Tgt.aim(text) == Tgt.Placed{Tgt.Bad{why}} : Tgt.Aim}

# LAW: so `git@host:path` stays a git URL, though it holds an `@`
law aim_scp:
  for +rest: String
  for e: {False{} == String.contains("git@" ++ rest, "://") : Bool}
  {Tgt.aim.named(Tgt.aim("git@" ++ rest)) == False{} : Bool}
