# pub/world: what `ez publish` reads. The directory the project is in
# (`here`), which git is asked about; the ledger's text, None when there is no
# ez.toml; and the answers to the questions the planner (pub/plan.bend)
# asked. There is no field for BEND_LIB, the hub or the clock, because the
# planner reads none of them.
#
# A question is one of the tool commands' own (tool/world.bend): `Locate` for
# what git says of the project, `git status --porcelain
# --untracked-files=normal` among it, and `Read` for a file the package walk
# asks for. Two are publish's: `Tracked`, every file git tracks under the
# project with its `git ls-files -v` tag, and `Upload`, `bend <entry>
# --publish`, with the `<name>@<version>` the ledger names the package by
# after it when it names one, run and what it printed. The upload is the one
# question whose answering is not a read: it sends the package, so the planner
# asks it last, once every check that can be made before it has passed.
import Base
import ../tool/world.bend as TW

# a question the planner asks
type Ask is Data:
  Tool{ask: TW.Ask}         # a file's text, or what git says of a path
  Tracked{}                 # `git ls-files -v` in the project
  Upload{entry: String, named: String}  # `bend <entry> --publish [<named>]`

# the answer to one: the tool commands' answer, or whether a program exited 0
# and what it printed
type Answer is Data:
  Told{answer: TW.Answer}
  Ran{ok: Bool, text: String}

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `ez publish` reads
type World is Data:
  World{here: String, ledger: Maybe<&2, String>, replies: List<&2, Reply>}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the directory the project is in
def here(world: World) -> String:
  World{h, _ledger, _replies} = world
  h

# the ledger's text, None when there is no ez.toml
def ledger(world: World) -> Maybe<&2, String>:
  World{_here, l, _replies} = world
  l

# every question answered so far
def replies(world: World) -> List<&2, Reply>:
  World{_here, _ledger, rs} = world
  rs

# the key a question is looked up by. A command uploads once, so the upload's
# key does not name the entry: the planner looks its answer up without
# knowing which entry the ledger names, and a law about that answer holds
# whatever the ledger says.
def key(ask: Ask) -> String:
  match ask:
    case Tool{q}:
      TW.key(q)
    case Tracked{}:
      "tracked"
    case Upload{_entry, _named}:
      "upload"

# an answer looked up, or none yet
type Heard is Data:
  Heard{answer: Answer}
  Open{}

# this answer when it is the question's, otherwise the rest's. The rest
# arrives as a thunk, so the first hit ends the scan.
def look.step(hit: Bool, answer: Answer, rest: Unit -> Heard) -> Heard:
  match hit:
    case True{}:
      Heard{answer}
    case False{}:
      rest(Unit{})

# the first answer given to a question
def look(rs: List<&2, Reply>, +want: String) -> Heard:
  match rs:
    case []:
      Open{}
    case Reply{ask, answer} <> t:
      look.step(String.eq(key(ask), want), answer, _u => look(t, want))

# the answer to a question, or none yet
def heard(+world: World, ask: Ask) -> Heard:
  look(replies(world), key(ask))
