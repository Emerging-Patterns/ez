# init/plan: `ez init` as a pure planner. It asks nothing: its World is the
# name, entry and description asked for and four texts, each None when the
# file is not there: ez.toml, `.gitignore`, the entry file and `src/lib.bend`.
# The interpreter (init/run.bend) reads them, calls `plan`, and runs what it
# returns.
#
# `ez init` starts a project and never writes over one. A ledger that is
# already there, whatever it holds, is refused with no effect at all, so its
# dependencies, tools and `bin` survive a second `ez init`. Otherwise the plan
# writes, in order: a new ledger naming the package and its entry; the
# ignore rules for what ez generates, added to `.gitignore` when it lacks
# them; `src/lib.bend`, when the stub below is written at the project's top
# and nothing is there yet; and a stub entry when there is none.
#
# The layout is cargo's: the program at the top and a library under `src/`
# that it imports, so the directory git would not keep empty holds a file. The
# stub opens with `# <name>: <description>`, since the hub describes a package
# by the first line of its first file by path (pub/blurb.bend), and the entry
# comes before anything under `src/`.
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), which
# the add design moves to a shared plan/plan.bend later; see "Update (A1,
# A4)" in docs/rfc/ez-add-planner.md.
import Base
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../pub/blurb.bend as B

# what `ez init` reads: the name, entry file and description asked for (""
# for none), and the texts of ez.toml, `.gitignore`, the entry file and
# `src/lib.bend`, None when absent
type World is Data:
  World{name: String, entry: String, desc: String, ledger: Maybe<&2, String>,
    ignore: Maybe<&2, String>, main: Maybe<&2, String>, lib: Maybe<&2, String>}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# where the ignore rules go
def ignore.file() -> String:
  ".gitignore"

# where the library a new project starts with goes
def lib.file() -> String:
  "src/lib.bend"

# the name a new ledger takes: what was asked for, or `app`
def name.or(+at: String) -> String:
  Bool.pick(String, String.is_empty(at), "app", at)

# the entry a new ledger names: what was asked for, or `main.bend`
def entry.or(+file: String) -> String:
  Bool.pick(String, String.is_empty(file), "main.bend", file)

# everything ez writes into a project that is not the project's: the vendored
# packages, the test gate's shadow and its cache all live under one `.ez/`, and
# `ez build` drops a binary in `bin/<name>.out` (`build.named` in
# ez/start.bend) unless it is told otherwise. A project whose first `ez check` leaves untracked output
# is a project whose owner has to work out for themselves which of it was
# theirs.
#
# `.ez/` is ignored as its contents rather than as a directory, and
# `.ez/lib` is let back in only to have its contents ignored again. That is
# what lets a `!.ez/lib/<hash>` line keep a vendored tree: git cannot
# re-include a file under a directory it has excluded, so under a bare
# `.ez/` every such line would be inert.
def rules(+name: String) -> List<&2, String>:
  [".ez/*", "!.ez/lib", ".ez/lib/*", "bin/" ++ name ++ ".out"]

# one step of a scan that is looking for one hit, with the head's answer in
# hand. `Bool.or` is an ordinary function and reduces both of its sides, so a
# scan written with it reads the whole list even when the first line answers.
# The rest of the scan arrives as a thunk and only the arm that wants it
# applies it.
def stated.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a file already states this rule, on a line of its own. A rule buried
# in a longer line is not the rule, so the comparison is against whole lines.
def stated(ls: List<&2, String>, +rule: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      stated.step(String.eq(String.trim(h), rule), _u => stated(t, rule))

# the rules a file does not already state, in order
def missing(rs: List<&2, String>, +ls: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = missing(t, ls)
      Bool.pick(List<&2, String>, stated(ls, h), more, h <> more)

# a file's text with a newline on the end, so what is appended to it starts on
# a line of its own. An empty file gets none, or the append would open with a
# blank line.
def tail(+text: String) -> String:
  Bool.pick(String, Bool.or(String.is_empty(text), String.ends_with(text, "\n")),
    text, text ++ "\n")

# the ignore file with the rules it lacks added under a line saying whose they
# are. What is already there is kept: the file is the project's, not ez's.
def ignored(+text: String, ms: List<&2, String>) -> String:
  tail(text) ++ "# written by ez\n" ++ String.join(ms, "\n") ++ "\n"

# the line a new entry opens with, which the hub shows as the package's
# description: the description asked for, or a placeholder that says one is
# still to be written. cargo writes no description into a new Cargo.toml; the
# hub has no field for one, so ours goes where the hub reads it.
def header(+name: String, +desc: String) -> String:
  "# " ++ name ++ ": " ++ Bool.pick(String, String.is_empty(desc), "TODO describe " ++ name, desc)

# the rest of a new entry: a program that checks and runs, saying what the
# library it was laid out with gives it, or `hello` when there is none
def body(lays: Bool) -> String:
  match lays:
    case True{}:
      "import Base\nimport ./src/lib.bend as Lib\n\ndef main() -> IO(Unit):\n  IO.print(Lib.greeting())\n"
    case False{}:
      "import Base\n\ndef main() -> IO(Unit):\n  IO.print(\"hello\")\n"

# the entry of a new project: its line for the hub, then the program
def stub(+name: String, +desc: String, lays: Bool) -> String:
  header(name, desc) ++ "\n" ++ body(lays)

# the library a new project starts with, which its entry imports
def lib() -> String:
  "import Base\n\n# what the program says\ndef greeting() -> String:\n  \"hello\"\n"

# a file's text, "" when it is not there
def text.of(got: Maybe<&2, String>) -> String:
  match got:
    case None{}:
      ""
    case Some{text}:
      text

# `.gitignore` written ahead of the rest when it lacks a rule. Nothing to add
# means nothing written, so an `ez init` in a directory whose ignore file
# already has the rules leaves it exactly as it found it.
def ignore.put(ms: List<&2, String>, +text: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match ms:
    case Nil{}:
      rest
    case Con{h, t}:
      P.Write{ignore.file(), ignored(text, h <> t)} <> rest

# whether the stub is written: nothing is at the entry, so `ez init` does not
# overwrite the program, and the entry is not ez.toml or `.gitignore`, so the
# stub is not written over the file this plan just wrote there
def due(got: Maybe<&2, String>, +at: String) -> Bool:
  match got:
    case Some{_s}:
      False{}
    case None{}:
      Bool.not(Bool.or(String.eq(at, toml()), String.eq(at, ignore.file())))

# whether `src/lib.bend` is laid out with the stub: nothing is there yet, so a
# library already there is never written over, the stub is written, and it
# sits at the project's top, where its `./src/lib.bend` import finds it. An
# entry in a directory of its own gets the stub alone.
def lays(got: Maybe<&2, String>, due: Bool, +at: String) -> Bool:
  match got:
    case Some{_s}:
      False{}
    case None{}:
      Bool.and(due, Bool.not(String.contains(at, "/")))

# the stub at the entry when it is due, ahead of the rest
def main.put(due: Bool, +at: String, +text: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match due:
    case True{}:
      P.Write{at, text} <> rest
    case False{}:
      rest

# the library when it is laid out, ahead of the rest
def lib.put(lays: Bool, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match lays:
    case True{}:
      P.Write{lib.file(), lib()} <> rest
    case False{}:
      rest

# the files written after the ledger and the ignore rules: the library and
# the stub, each when it is due
def files(
  +name: String,
  +at: String,
  +desc: String,
  main: Maybe<&2, String>,
  lib: Maybe<&2, String>
) -> List<&2, P.Effect>:
  +d = due(main, at)
  +l = lays(lib, d, at)
  lib.put(l, main.put(d, at, stub(name, desc, l), []))

# the ledger a new project starts from: this package, its entry, and nothing
# else, so no `publish-as` or `version` and a project that publishes by hash
def model(+name: String, +at: String) -> M.Manifest:
  M.Manifest{name, at, "", "", "", "", [], []}

# its text
def fresh(+name: String, +at: String) -> String:
  Rend.show(model(name, at))

# whether a new project can be written: its ledger reads back (EZ-LED-4),
# and the line its entry opens with is one line, so the description cannot
# spill into the program
def fits(+name: String, +at: String, +desc: String) -> Bool:
  Bool.and(Rend.renderable(model(name, at)), Bool.not(B.has.nl(header(name, desc))))

# why a new project that does not fit is refused
def why.unfit(+name: String, +at: String) -> String:
  Bool.pick(String, Rend.renderable(model(name, at)),
    "ez: a description is one line, the first line of the entry, and this one holds a newline",
    Rend.unrenderable())

# the new project's files, once it fits. A name or entry the ledger cannot
# carry, such as one holding a quote, or a description holding a newline, is
# refused with no effect at all.
def plan.new(
  ok: Bool,
  +name: String,
  +at: String,
  +desc: String,
  ignore: Maybe<&2, String>,
  main: Maybe<&2, String>,
  lib: Maybe<&2, String>
) -> P.Plan:
  match ok:
    case True{}:
      +text = text.of(ignore)
      P.Plan{P.Write{toml(), fresh(name, at)} <>
        ignore.put(missing(rules(name), String.lines(text)), text,
          files(name, at, desc, main, lib)), P.Success{}}
    case False{}:
      P.Plan{[], P.Refused{why.unfit(name, at)}}

# the plan, once the name and entry are settled. A ledger on disk holds
# dependencies, tools and a `bin` that a fresh one would lose, so `ez init`
# writes over none of it, whatever the file holds, and refuses.
def plan.go(
  led: Maybe<&2, String>,
  +name: String,
  +at: String,
  +desc: String,
  ignore: Maybe<&2, String>,
  main: Maybe<&2, String>,
  lib: Maybe<&2, String>
) -> P.Plan:
  match led:
    case Some{_s}:
      P.Plan{[], P.Refused{"ez: " ++ toml() ++
        " already exists; ez init writes a new project and leaves it alone"}}
    case None{}:
      plan.new(fits(name, at, desc), name, at, desc, ignore, main, lib)

# `ez init` over a World
def plan(world: World) -> P.Plan:
  World{n, e, d, led, ig, mn, lb} = world
  plan.go(led, name.or(n), entry.or(e), d, ig, mn, lb)

# whether a plan ends in a refusal
def refuses.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether `ez init` refuses on a World
def refuses(world: World) -> Bool:
  refuses.plan(plan(world))
