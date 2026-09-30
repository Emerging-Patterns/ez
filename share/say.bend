# share/say: the words a long step says. The mark drawn while it runs is
# share/spin.bend: a child process, started with its own session and its
# standard streams closed, so it opens the terminal by the path this process's
# own stderr or stdout already has. A pipe is not a terminal: the line is
# printed once and left, which is what a log wants.
import Base
import ../pkg/path.bend as P

# a spinner that is running, or none. An empty pid means the line was already
# printed and nothing has to be stopped. `msg` is what the terminal is owed
# when the mark is cleared.
type Spin is Data:
  Spin{dev: String, pid: String, msg: String}

# the first twelve characters of a commit, which is enough to tell one from
# the next. A shorter name is already short.
def brief.go(short: Bool, +rev: String) -> String:
  match short:
    case True{}:
      rev
    case False{}:
      String.take(rev, 12n)

# a commit as a line shows it
def brief(+rev: String) -> String:
  brief.go(Nat.is_le(String.length(rev), 12n), rev)

# a package's name when its entry has one, otherwise the hash. `main` is kept:
# it is the name the file has.
def label.go(empty: Bool, +hash: String, +name: String) -> String:
  match empty:
    case True{}:
      hash
    case False{}:
      name

# what a line calls a package
def label(+hash: String, +entry: String) -> String:
  +name = P.unbend(P.base(entry))
  label.go(String.is_empty(name), hash, name)

# `dep sha256: git fetch (https://github.com/…)`
def dep.git(+name: String, +url: String) -> String:
  "dep " ++ name ++ ": git fetch (" ++ url ++ ")"

# a package taken from the hub
def dep.hub(+name: String) -> String:
  "dep " ++ name ++ ": hub fetch"

# a binary already built for this commit
def reused(+name: String) -> String:
  name ++ ": cached"

# the lock resolving every dependency
def resolving() -> String:
  "resolving deps"

def resolving.at(+name: String) -> String:
  "resolving " ++ name

def git.fetch(+url: String) -> String:
  "git fetch (" ++ url ++ ")"

# a binary being built
def building(+name: String) -> String:
  "building " ++ name

# a binary being linked into place
def linking(+at: String) -> String:
  "linking " ++ at

# a binary built and linked
def installed(+name: String, +at: String) -> String:
  "installed " ++ name ++ " -> " ++ at

# a binary linked, with nothing to build
def linked(+name: String, +at: String) -> String:
  "linked " ++ name ++ " -> " ++ at

# a commit's tree being weighed for its NAR hash
def hashing(+rev: String) -> String:
  "hashing " ++ brief(rev)

# a device path that is a terminal. A pipe and `/dev/null` are not.
def tty.at(+path: String) -> Bool:
  Bool.or(String.starts_with(path, "/dev/pts/"),
    Bool.or(String.eq(path, "/dev/console"), String.starts_with(path, "/dev/tty")))

def tty.out(on: Bool, +out: String) -> String:
  match on:
    case True{}:
      out
    case False{}:
      ""

# stderr's terminal when it is one, otherwise stdout's, otherwise none
def tty.pick.go(on: Bool, +err: String, +out: String) -> String:
  match on:
    case True{}:
      err
    case False{}:
      tty.out(tty.at(out), out)

def tty.pick(+err: String, +out: String) -> String:
  tty.pick.go(tty.at(err), err, out)

# the hub answered 404 for a manifest. A missing file is a different miss:
# its path is not `/manifest`.
def hub.miss(+why: String) -> Bool:
  Bool.and(String.contains(why, "/manifest:"),
    String.ends_with(why, "the server answered 404"))

def hub.explain.go(miss: Bool, +hash: String, +url: String, +why: String) -> String:
  match miss:
    case True{}:
      "ez: " ++ hash ++ ": the hub has no manifest for this package (" ++ url ++
        " answered 404). Re-lock with `ez lock`, fix the dependency, or vendor it offline (`ez add`)."
    case False{}:
      "ez: " ++ why

def hub.explain(+hash: String, +url: String, +why: String) -> String:
  hub.explain.go(hub.miss(why), hash, url, why)

# the commit the words name. A tag is what a person pinned; a bare rev is not.
def drift.where(bare: Bool, +tag: String, +rev: String) -> String:
  match bare:
    case True{}:
      "commit " ++ rev
    case False{}:
      "tagged commit " ++ tag ++ " (" ++ rev ++ ")"

# the tagged commit's tree no longer hashes to the pin. Upgrade will not
# invent a new hash for that: the pin is what the ledger says, and a drift
# is the ledger and the tree disagreeing.
def drift(+name: String, +tag: String, +rev: String, +old: String, +new: String) -> String:
  "ez: " ++ name ++ ": the tree hash of " ++
    drift.where(String.is_empty(tag), tag, rev) ++
    " no longer matches the pin (the package moved, or the hash is wrong: " ++
    old ++ " on the pin, " ++ new ++
    " in the tree). `ez lock --upgrade` cannot fix a drifted pin. Update the dependency hash, re-add the package, or check the tag."

# a drift judged before the tree was weighed, so there are not two hashes to show
def stuck(+name: String) -> String:
  "ez: " ++ name ++
    ": the pin drifted. `ez lock --upgrade` cannot fix a drifted pin. Update the dependency hash, re-add the package, or check the tag."

# a `[tools.` section in the ledger text. The parser is not asked: a ledger
# that does not parse can still have named the command.
def has.tools(+text: String) -> Bool:
  String.contains(text, "[tools.")

# `ez sync` is not a command. A ledger that pins tools already has the one
# that builds them; a ledger that does not is pointed at lock and install.
def hint(tools: Bool) -> String:
  match tools:
    case True{}:
      "hint: `sync` is not a command; use `ez tool sync`"
    case False{}:
      "hint: `sync` is not a command. Use `ez lock` to resolve dependencies, or `ez tool install <target>` to link a binary."
