# pub/pub: `ez publish`. The package is sent to the hub by `bend --publish`,
# which is the only thing that can send it, but the `0x` name ez reports is
# the one `pkg/pkg.bend` computed from the file set and never the one bend
# printed. Reading bend's output is a check, not a lookup: ez already knows
# the answer before bend runs, and what bend says is compared against it.
#
# That distinction is the whole command. A hash grepped out of another
# program's stdout is a hash you have no independent reason to believe, and a
# loose pattern with a looser fallback behind it turns a bend that changed its
# wording into a wrong hash written quietly into a README. So the recogniser
# here is anchored, matching a line that is a `0x` name and nothing else, and
# an output it cannot read is an error that stops the command, exactly like an
# output that names a different package. Both mean a walk has drifted, ez's or
# bend's, and that is worth finding out about loudly.
#
# Publishing is irreversible and public, so it refuses before it does anything
# if git reports the working tree dirty. See `dirty` below for what dirty
# means and why.
#
# bend's own update nag is `ez/quiet.bend`'s business and needs no help here:
# `is_name` is anchored at both ends, so a line that is not a bare `0x` name
# is not an answer however it reads.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P
import ../git/git.bend as G

# what reading bend's own answer came to. `Agreed` carries no hash: the value
# ez reports is ez's, so there is nothing for this to hand back.
type Said is Data:
  Agreed{}
  Unread{}
  Differs{theirs: String}

# how many characters a `0x` name is written with: the two of the prefix and
# the thirty-two `pkg/pkg.bend`'s `hash_of` takes off a sha256
def name.length() -> Nat:
  34n

# whether a line is a `0x` package name and nothing else. Anchored at both
# ends: the prefix, the exact length, and every character after the prefix one
# a lowercase hex digest may hold. `git/git.bend` already walks a hex string
# for `is_rev` and its walk is the one proved to stop at the first character
# that is not hex, so it is reused rather than written again.
#
# Both other lines bend prints around its answer fail this, and `pub/LAWS.bend`
# says so rather than leaving it to a reading of bend's source:
# `publishing N files, ... as 0x... (mining its proof of work)` and
# `import 0x.../entry.bend as Name` each start with something that is not `0x`.
def is_name(+word: String) -> Bool:
  Bool.and(String.starts_with(word, "0x"),
    Bool.and(Nat.is_eq(String.length(word), name.length()),
      G.hex.all(String.to_list(String.drop(word, 2n)))))

# one step of the search, with the head's answer in hand. `Bool.pick` is an
# ordinary function and builds both arms before it picks one, so a search
# written with it never stops at the line it found. The rest arrives as a
# thunk and only the arm that wants it applies it.
def answer.step(here: Bool, line: String, rest: Unit -> String) -> String:
  match here:
    case True{}:
      line
    case False{}:
      rest(Unit{})

# the line of bend's output that is a name, or "" when no line is. There is no
# second pattern behind this one: an output with no bare name in it answers
# nothing, and `publish.said` below turns that into an error.
def answer(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      answer.step(is_name(h), h, _u => answer(t))

# the two hashes compared, with bend's already recognised
def judge.go(same: Bool, theirs: String) -> Said:
  match same:
    case True{}:
      Agreed{}
    case False{}:
      Differs{theirs}

# an answer that is not a name is not an answer, whatever ez computed. This
# arm is the one the bash version did not have: it fell back to a looser
# pattern instead, and a looser pattern always finds something.
def judge.said(found: Bool, +ours: String, +theirs: String) -> Said:
  match found:
    case False{}:
      Unread{}
    case True{}:
      judge.go(String.eq(ours, theirs), theirs)

# bend's answer weighed against ez's hash
def judge.at(+ours: String, +theirs: String) -> Said:
  judge.said(is_name(theirs), ours, theirs)

# what bend's output says about the package ez computed
def judge(+ours: String, ls: List<&2, String>) -> Said:
  judge.at(ours, answer(ls))

# whether a verdict lets the command go on. Only one of the three does.
def agreed(reply: Said) -> Bool:
  match reply:
    case Agreed{}:
      True{}
    case Unread{}:
      False{}
    case Differs{_theirs}:
      False{}

# one line of `git status --porcelain` weighed, with the rest of the walk
# behind a thunk so a status that names a hundred files stops at the first.
# Every line git prints there names a path whose state on disk is not the
# state the commit holds, so every one of them counts, whatever its two-letter
# code says, `??` for an untracked file included. See `dirty` for why that one
# is not an exception.
def dirty.step(blank: Bool, rest: Unit -> Bool) -> Bool:
  match blank:
    case True{}:
      rest(Unit{})
    case False{}:
      True{}

# whether any line of the status says anything. The only empty line git status
# ever produces is the one `String.lines` makes of the trailing newline, so an
# empty line is the absence of a change rather than a change with no name.
def dirty.lines(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      False{}
    case +h <> t:
      dirty.step(String.is_empty(h), _u => dirty.lines(t))

# one line of the other walk, the same way round
def blanks.step(blank: Bool, rest: Unit -> Bool) -> Bool:
  match blank:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether the status named nothing. Stated as its own walk rather than as the
# negation of the one above, so `pub/LAWS.bend` can hold the two to each other:
# a tree is clean exactly when git named no path at all.
def blanks(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case +h <> t:
      blanks.step(String.is_empty(h), _u => blanks(t))

# whether the working tree holds anything a commit does not.
#
# Dirty is exactly "`git status --porcelain` printed a line". Three edge cases
# were decided rather than fallen into:
#
# Ignored files are not dirty, and that is the point of the rule rather than a
# hole in it. `.ez/`, `bin/ez.bin` and the gate's own output are gitignored, so
# git never names them, so a project that has just built or tested can still
# publish. Nothing here re-adds them: what is ignored is the project's call,
# written down in its own `.gitignore`, and ez is not the one to overrule it.
#
# Untracked files that are not ignored *are* dirty. They are the case worth
# getting right: the package's file set is read off the working tree, so an
# untracked `.bend` file the entry imports is uploaded to the hub though no
# commit anywhere holds it, and the import line ez then prints names a package
# nobody can ever rebuild. Refusing is the only answer that keeps the promise
# the command makes.
#
# A directory that is no git repo at all is neither clean nor dirty: git exits
# non-zero saying so, and `status` below stops the command with what git said,
# the way `git/git.bend` stops on any other failed git command. `ez publish`
# promises that what went to the hub exists in a commit; with no repository
# there is no commit to point at, and a promise that cannot be kept is not one
# to make quietly.
def dirty(text: String) -> Bool:
  dirty.lines(String.lines(text))

# git's verdict on the working tree, or the command stopped with whatever git
# said. `--untracked-files=normal` is passed rather than left to the default
# because `status.showUntrackedFiles=no` in a config would otherwise hide the
# very files this refuses for.
def status.said(ok: Bool, +text: String) -> IO(String):
  match ok:
    case False{}:
      IO.die(String, 1, "ez: git status: " ++ text)
    case True{}:
      IO.pure(String, text)

# what git says the working tree holds
def status() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["git", "status", "--porcelain",
      "--untracked-files=normal"])
    status.said(R.ok(out), R.text(out))

# a tree with anything uncommitted in it stops the command before anything is
# sent. The lines git printed come with the refusal, since the next question is
# always which file.
def clean.said(bad: Bool, +text: String) -> IO(Unit):
  match bad:
    case True{}:
      IO.die(Unit, 1, "ez: the working tree is dirty, and publishing is " ++
        "public and cannot be taken back, so what goes to the hub has to " ++
        "exist in a commit. git status says:\n" ++ text)
    case False{}:
      IO.pure(Unit, Unit{})

# the working tree asked about, and the command stopped if it answers
def clean() -> IO(Unit):
  do IO<Unit>:
    +text : String <- status()
    clean.said(dirty(text), text)

# the hash, and then the import line a consumer would write, which is the thing
# a person actually does something with. The same two lines `git/git.bend`'s
# `said` prints after vendoring, and the alias is named the same way.
def said(+hash: String, +entry: String) -> IO(Unit):
  +base = P.base(entry)
  do IO<Unit>:
    IO.print(hash)
    IO.print("import " ++ hash ++ "/" ++ base ++ " as " ++
      G.title(P.unbend(base)))

# what a disagreement says. Both numbers are named because the next question is
# which walk drifted, and neither is reported as the package's name: the
# command exits non-zero and prints no import line, so nothing downstream of it
# can mistake either for an answer.
def sent.differs(+ours: String, +theirs: String) -> IO(Unit):
  IO.die(Unit, 1, "ez: ez computed " ++ ours ++ " and bend published " ++
    theirs ++ ". One of the two package walks has drifted from the other, " ++
    "so neither name is safe to write down and ez has reported none.")

# what an unreadable output says. bend published, so the upload already
# happened, but ez cannot confirm what it published, and an unconfirmed hash is
# the thing this command exists not to print.
def sent.unread(+text: String) -> IO(Unit):
  IO.die(Unit, 1, "ez: bend printed no line that is a 0x name, so there is " ++
    "nothing to check ez's hash against. bend said:\n" ++ text)

# the verdict acted on
def sent(reply: Said, +ours: String, +entry: String, +text: String) -> IO(Unit):
  match reply:
    case Agreed{}:
      said(ours, entry)
    case Unread{}:
      sent.unread(text)
    case Differs{theirs}:
      sent.differs(ours, theirs)

# a `bend --publish` that failed fails the command with what bend said. Only a
# run that finished has an answer worth checking.
def publish.said(ok: Bool, +ours: String, +entry: String, +text: String) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, "ez: bend " ++ entry ++ " --publish: " ++ text)
    case True{}:
      sent(judge(ours, String.lines(text)), ours, entry, text)

# the upload itself, with the project's packages on BEND_LIB the way every
# other `bend` ez starts has them
def publish.run(+lib: String, +entry: String, +ours: String) -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(["env", "BEND_LIB=" ++ lib, "bend", entry,
      "--publish"])
    publish.said(R.ok(out), ours, entry, R.text(out))

# the entry published: the tree checked first, then ez's own hash computed from
# the file set, then bend run, then bend's answer checked against ez's. The
# order is the point: nothing is sent until the tree is clean, and nothing is
# reported until the two agree.
def publish(+lib: String, +entry: String) -> IO(Unit):
  do IO<Unit>:
    clean()
    +p : K.Pkg <- K.pkg_of(entry)
    publish.run(lib, entry, K.pkg.hash(p))
