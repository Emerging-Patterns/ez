# init/plan: `ez init` as a pure planner. It asks nothing: its World is the
# name and entry asked for and three texts, each None when the file is not
# there: ez.toml, `.gitignore`, and the entry file. The interpreter
# (init/run.bend) reads them, calls `plan`, and runs what it returns.
#
# `ez init` starts a project and never writes over one. A ledger that is
# already there, whatever it holds, is refused with no effect at all, so its
# dependencies, tools and `bin` survive a second `ez init`. Otherwise the plan
# writes, in order: a new ledger naming the package and its entry; the
# ignore rules for what ez generates, added to `.gitignore` when it lacks
# them; and a stub entry when there is none.
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), which
# the add design moves to a shared plan/plan.bend later; see "Update (A1,
# A4)" in docs/rfc/ez-add-planner.md.
import Base
import ../lock/plan.bend as P
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend

# what `ez init` reads: the name and entry file asked for ("" for none), and
# the texts of ez.toml, `.gitignore` and the entry file, None when absent
type World is Data:
  World{name: String, entry: String, ledger: Maybe<&2, String>,
    ignore: Maybe<&2, String>, main: Maybe<&2, String>}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# where the ignore rules go
def ignore.file() -> String:
  ".gitignore"

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

# the entry of a new project: a program that checks and runs
def stub() -> String:
  "import Base\n\ndef main() -> IO(Unit):\n  IO.print(\"hello\")\n"

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

# the stub, unless the entry is one of the files the plan writes itself
def main.write(taken: Bool, +at: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match taken:
    case True{}:
      rest
    case False{}:
      P.Write{at, stub()} <> rest

# the stub written when nothing is at the entry, ahead of the rest. An entry
# that is already there is left alone, so `ez init` does not overwrite the
# program; nor is an entry named ez.toml or `.gitignore` written over the
# file this plan just wrote there.
def main.put(got: Maybe<&2, String>, +at: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match got:
    case Some{_s}:
      rest
    case None{}:
      main.write(Bool.or(String.eq(at, toml()), String.eq(at, ignore.file())), at, rest)

# the ledger a new project starts from: this package, its entry, and nothing
# else, so no `publish-as` or `version` and a project that publishes by hash
def model(+name: String, +at: String) -> M.Manifest:
  M.Manifest{name, at, "", "", "", "", [], []}

# its text
def fresh(+name: String, +at: String) -> String:
  Rend.show(model(name, at))

# the new project's files, once its ledger is known to read back. A name or
# entry the ledger cannot carry, such as one holding a quote, is refused with
# no effect at all (EZ-LED-4).
def plan.new(
  ok: Bool,
  +name: String,
  +at: String,
  ignore: Maybe<&2, String>,
  main: Maybe<&2, String>
) -> P.Plan:
  match ok:
    case True{}:
      +text = text.of(ignore)
      P.Plan{P.Write{toml(), fresh(name, at)} <>
        ignore.put(missing(rules(name), String.lines(text)), text,
          main.put(main, at, [])), P.Success{}}
    case False{}:
      P.Plan{[], P.Refused{Rend.unrenderable()}}

# the plan, once the name and entry are settled. A ledger on disk holds
# dependencies, tools and a `bin` that a fresh one would lose, so `ez init`
# writes over none of it, whatever the file holds, and refuses.
def plan.go(
  led: Maybe<&2, String>,
  +name: String,
  +at: String,
  ignore: Maybe<&2, String>,
  main: Maybe<&2, String>
) -> P.Plan:
  match led:
    case Some{_s}:
      P.Plan{[], P.Refused{"ez: " ++ toml() ++
        " already exists; ez init writes a new project and leaves it alone"}}
    case None{}:
      plan.new(Rend.renderable(model(name, at)), name, at, ignore, main)

# `ez init` over a World
def plan(world: World) -> P.Plan:
  World{n, e, led, ig, mn} = world
  plan.go(led, name.or(n), entry.or(e), ig, mn)

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
