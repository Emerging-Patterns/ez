# ez/say: the words a long step says, and a spinner for the wait.
#
# A clone, a hub fetch or a native build can sit there for half a minute, and
# a step that prints nothing looks stopped. The line is printed before the
# work. On a terminal it is drawn again in place, with a mark that moves,
# until the step finishes; the mark is a child, because the work itself is
# one program waited on to the end and nothing can be printed while it runs.
# That child is started with its own session and its standard streams closed,
# so it opens the terminal by the path this process's own stderr or stdout
# already has. A pipe is not a terminal: the line is printed once and left,
# which is what a log wants.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
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

def label(+hash: String, +entry: String) -> String:
  +name = P.unbend(P.base(entry))
  label.go(String.is_empty(name), hash, name)

# `dep sha256: git fetch (https://github.com/…)`
def dep.git(+name: String, +url: String) -> String:
  "dep " ++ name ++ ": git fetch (" ++ url ++ ")"

# a package taken from the hub
def dep.hub(+name: String) -> String:
  "dep " ++ name ++ ": hub fetch"

# a tree already laid out, so nothing is fetched
def dep.cached(+name: String) -> String:
  "dep " ++ name ++ ": cached"

# a checkout or a pin that did not move
def kept(+name: String) -> String:
  name ++ ": unchanged"

# a binary already built for this commit
def reused(+name: String) -> String:
  name ++ ": cached"

def resolving() -> String:
  "resolving deps"

def resolving.at(+name: String) -> String:
  "resolving " ++ name

def fetching(+label: String, +rev: String) -> String:
  "fetching " ++ label ++ "@" ++ brief(rev)

def git.fetch(+url: String) -> String:
  "git fetch (" ++ url ++ ")"

def building(+name: String) -> String:
  "building " ++ name

def linking(+at: String) -> String:
  "linking " ++ at

def installed(+name: String, +at: String) -> String:
  "installed " ++ name ++ " -> " ++ at

def linked(+name: String, +at: String) -> String:
  "linked " ++ name ++ " -> " ++ at

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

# the parent's fd, by number. The child cannot look at its own: that one was
# replaced with a pipe before this ran. `$1` is the number.
def probe() -> String:
  "ppid=; while read -r k v; do case $k in PPid:) ppid=$v;; esac; done < /proc/self/status; readlink /proc/$ppid/fd/$1 2>/dev/null"

# a mark on the terminal while the parent is alive. `$1` is the terminal,
# `$2` the line. The mark walks ⠋ ⠙ ⠹ ⠸ ⠼ ⠴ ⠦ ⠧ ⠇ ⠏. An empty parent
# id exits rather than spinning on `/proc`.
def frames() -> String:
  "ppid=; while read -r k v; do case $k in PPid:) ppid=$v;; esac; done < /proc/self/status; [ -n \"$ppid\" ] || exit 0; while [ -d /proc/$ppid ]; do printf '\\r%s %s' '⠋' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠙' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠹' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠸' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠼' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠴' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠦' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠧' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠇' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠏' \"$2\" >\"$1\"; sleep 0.08; done"

# the mark wiped, and the line left in its place
def settle() -> String:
  "printf '\\r\\033[K%s\\n' \"$2\" >\"$1\""

# one fd of this process, as a path. A failure is not a terminal.
def link(+fd: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["sh", "-c", probe(), "sh", fd])
    return String.trim(R.text(out))

def dev() -> IO(String):
  do IO<String>:
    +err : String <- link("2")
    +out : String <- link("1")
    return tty.pick(err, out)

# the mark, when there is a terminal to draw it on
def start(on: Bool, +dev: String, +msg: String) -> IO(Spin):
  match on:
    case False{}:
      IO.pure(Spin, Spin{"", "", ""})
    case True{}:
      do IO<Spin>:
        +pid : String <- R.start(["sh", "-c", frames(), "sh", dev, msg])
        return Spin{dev, String.trim(pid), msg}

def hold.at(plain: Bool, +dev: String, +msg: String) -> IO(Spin):
  match plain:
    case True{}:
      do IO<Spin>:
        IO.print_err(msg)
        return Spin{"", "", ""}
    case False{}:
      start(True{}, dev, msg)

# the line, then the mark when a terminal will show it moving. A pipe gets
# the line and nothing else.
def hold(+msg: String) -> IO(Spin):
  do IO<Spin>:
    +tty : String <- dev()
    hold.at(String.is_empty(tty), tty, msg)

# a spinner that never started still owes its line, unless the plain path
# already printed it and left the message empty
def owed(empty: Bool, +msg: String) -> IO(Unit):
  match empty:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print_err(msg)

# the mark stopped, and the line written where it was
def done.live(+dev: String, +pid: String, +msg: String) -> IO(Unit):
  do IO<Unit>:
    _k : String <- R.exec(["kill", pid])
    _s : String <- R.exec(["sh", "-c", settle(), "sh", dev, msg])
    return Unit{}

def done.bad(bad: Bool, +dev: String, +pid: String, +msg: String) -> IO(Unit):
  match bad:
    case True{}:
      owed(String.is_empty(msg), msg)
    case False{}:
      done.live(dev, pid, msg)

def done(s: Spin) -> IO(Unit):
  Spin{+dev, +pid, +msg} = s
  done.bad(Bool.or(String.is_empty(pid), String.eq(pid, "0")), dev, pid, msg)
