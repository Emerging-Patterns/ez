# manifest/ignore: the gitignore allowlist, derived from the ledger. A
# dependency marked `vendor = true` has its tree committed under
# `.ez/lib/<hash>`, and git only keeps it when `.gitignore` says so with a
# `!.ez/lib/<hash>` line. That line has to follow the ledger exactly: a hash
# the ledger stopped naming leaves a dead tree committed, and one it names
# but the file does not is a tree a clone never gets. So the allowlist is not
# edited, it is derived: `sync` takes the ledger's dependencies and the file,
# and gives back the file whose allowlist lines are exactly the vendored
# hashes, with every line that is not ez's left as it was. `ez add`,
# `ez remove` and `ez lock --upgrade` all write what it returns.
#
# Which lines are ez's. A line that starts `!.ez/lib/` is ez's allowlist, as
# written, and whatever follows the prefix is the hash it names. Anything
# else is read loosely: surrounding blanks trimmed, one leading `/` and one
# trailing `/` dropped, so `!/.ez/lib/<h>/` and `  !.ez/lib/<h>` are
# allowlist lines too. ez owns everything under `.ez/lib`, so any exception
# under it is ez's to keep or drop; a line spelled differently from `allow`
# is dropped and the hash, when the ledger still vendors it, written back in
# the canonical spelling. Three more lines are what makes the allowlist work
# at all: `.ez/*`, `!.ez/lib` and `.ez/lib/*`. Git cannot re-include a file
# under a directory it excluded, so a bare `.ez/` (or `.ez`, `/.ez/`) makes
# every allowlist line inert. That line is replaced, where it stands, by
# whichever of the three the file does not already have.
#
# Where the allowlist goes. The vendored hashes are written as one block, in
# the ledger's order, where the file's first allowlist line was. A file with
# none gets the block at its end, which is where the upgrade has always
# appended one, preceded by whichever of the three rules the file lacks.
import Base
import ./manifest.bend as M

# what one line of an ignore file is to ez
type Rule is Data:
  Other{}
  Dir{}
  Star{}
  Lib{}
  Pkgs{}
  Allow{hash: String}

# a line, with what it is to ez beside it
type Line is Data:
  Line{kind: Rule, text: String}

# the gitignore line that keeps one committed tree
def allow(+hash: String) -> String:
  "!.ez/lib/" ++ hash

# one leading `/`, which anchors a pattern to the file's own directory and
# so changes nothing for a `.gitignore` at the root
def lead(+pat: String) -> String:
  Bool.pick(String, String.starts_with(pat, "/"), String.drop(pat, 1n), pat)

# one trailing `/`, which only narrows a pattern to directories, and every
# path ez names here is one
def trail(+pat: String) -> String:
  Bool.pick(String, String.ends_with(pat, "/"),
    String.take(pat, Nat.sub(String.length(pat), 1n)), pat)

# a pattern with both of those dropped
def bare(+pat: String) -> String:
  trail(lead(pat))

# an exception under `.ez/lib/` names the hash after the prefix
def loose.under(under: Bool, +rest: String) -> Rule:
  match under:
    case True{}:
      Bool.pick(Rule, String.is_empty(rest), Other{}, Allow{rest})
    case False{}:
      Other{}

# an exception: the re-included library directory, or one tree under it
def loose.neg(+pat: String) -> Rule:
  Bool.pick(Rule, String.eq(pat, ".ez/lib"), Lib{},
    loose.under(String.starts_with(pat, ".ez/lib/"), String.drop(pat, 8n)))

# an exclusion: the whole of `.ez`, what is inside it, or what is inside
# its library directory
def loose.pos(+pat: String) -> Rule:
  Bool.pick(Rule, String.eq(pat, ".ez"), Dir{},
    Bool.pick(Rule, String.eq(pat, ".ez/*"), Star{},
      Bool.pick(Rule, String.eq(pat, ".ez/lib/*"), Pkgs{}, Other{})))

# a trimmed line, read by whether it is an exception
def loose.go(neg: Bool, +pat: String) -> Rule:
  match neg:
    case True{}:
      loose.neg(bare(String.drop(pat, 1n)))
    case False{}:
      loose.pos(bare(pat))

# a line that is not written the way `allow` writes one
def loose(+line: String) -> Rule:
  +pat = String.trim(line)
  loose.go(String.starts_with(pat, "!"), pat)

# `!.ez/lib/` with nothing after it is the directory, with a trailing slash
def canon(empty: Bool, +rest: String) -> Rule:
  match empty:
    case True{}:
      Lib{}
    case False{}:
      Allow{rest}

# a line written the way `allow` writes one names the hash after the prefix
def kind.go(exact: Bool, +line: String) -> Rule:
  match exact:
    case True{}:
      canon(String.is_empty(String.drop(line, 9n)), String.drop(line, 9n))
    case False{}:
      loose(line)

# what a line of an ignore file is to ez
def kind(+line: String) -> Rule:
  kind.go(String.starts_with(line, "!.ez/lib/"), line)

# every line, with what it is
def tag(ls: List<&2, String>) -> List<&2, Line>:
  match ls:
    case []:
      []
    case +h <> t:
      Line{kind(h), h} <> tag(t)

# the hash an allowlist line names, in front of the rest
def hashes.put(what: Rule, rest: List<&2, String>) -> List<&2, String>:
  match what:
    case Allow{h}:
      h <> rest
    case Other{}:
      rest
    case Dir{}:
      rest
    case Star{}:
      rest
    case Lib{}:
      rest
    case Pkgs{}:
      rest

# every hash the allowlist lines of a file name, in order. This is what the
# allowlist says, and what the laws hold against the ledger.
def hashes(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      hashes.put(kind(h), hashes(t))

# a line that is not ez's, in front of the rest
def others.put(what: Rule, +line: String, rest: List<&2, String>) -> List<&2, String>:
  match what:
    case Other{}:
      line <> rest
    case Allow{_h}:
      rest
    case Dir{}:
      rest
    case Star{}:
      rest
    case Lib{}:
      rest
    case Pkgs{}:
      rest

# every line that is not ez's, in order: the lines `sync` must not touch
def others(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      others.put(kind(h), h, others(t))

# a hash joins the allowlist only when there is one. `M.parse` refuses a
# dependency with no hash, so this only guards a model built by hand.
def vended.hash(empty: Bool, +hash: String, rest: List<&2, String>) -> List<&2, String>:
  match empty:
    case True{}:
      rest
    case False{}:
      hash <> rest

# a dependency joins the allowlist only when its tree is committed
def vended.put(vend: Bool, +hash: String, rest: List<&2, String>) -> List<&2, String>:
  match vend:
    case True{}:
      vended.hash(String.is_empty(hash), hash, rest)
    case False{}:
      rest

# the hashes the allowlist must name: every dependency marked `vendor = true`,
# in the order the ledger wrote them
def vended(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      vended.put(M.source.vendor(M.source.dep(h)), M.dep.hash(h), vended(t))

# the same walk as `vended`, writing each hash's line
def allows.hash(empty: Bool, +hash: String, rest: List<&2, String>) -> List<&2, String>:
  match empty:
    case True{}:
      rest
    case False{}:
      allow(hash) <> rest

# a dependency's line, when its tree is committed
def allows.put(vend: Bool, +hash: String, rest: List<&2, String>) -> List<&2, String>:
  match vend:
    case True{}:
      allows.hash(String.is_empty(hash), hash, rest)
    case False{}:
      rest

# the allowlist lines of a ledger, in its order
def allows(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      allows.put(M.source.vendor(M.source.dep(h)), M.dep.hash(h), allows(t))

# whether two kinds are the same rule. Two allowlist lines are never asked.
def same(left: Rule, right: Rule) -> Bool:
  match left right:
    case Dir{} Dir{}:
      True{}
    case Star{} Star{}:
      True{}
    case Lib{} Lib{}:
      True{}
    case Pkgs{} Pkgs{}:
      True{}
    case _ _:
      False{}

# the rest of the scan only when this line was not it
def has.step(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a file already has a line of this kind
def has(ls: List<&2, Line>, +want: Rule) -> Bool:
  match ls:
    case []:
      False{}
    case Line{+what, _text} <> t:
      has.step(same(what, want), _u => has(t, want))

# a rule, in front of the rest, when the file does not have it
def rule.put(there: Bool, +line: String, rest: List<&2, String>) -> List<&2, String>:
  match there:
    case True{}:
      rest
    case False{}:
      line <> rest

# the three rules the allowlist needs, less the ones already there
def rules.go(star: Bool, lib: Bool, pkgs: Bool) -> List<&2, String>:
  rule.put(star, ".ez/*", rule.put(lib, "!.ez/lib", rule.put(pkgs, ".ez/lib/*", [])))

# the rules a file lacks
def rules(+ls: List<&2, Line>) -> List<&2, String>:
  rules.go(has(ls, Star{}), has(ls, Lib{}), has(ls, Pkgs{}))

# the rules go in front of the block only when nothing else puts them in: a
# `.ez/` line is replaced by them where it stands, and a ledger that vendors
# nothing needs none
def need(skip: Bool, +rs: List<&2, String>) -> List<&2, String>:
  match skip:
    case True{}:
      []
    case False{}:
      rs

# the allowlist block: the missing rules, then one line per vendored hash
def block(+ds: List<&2, M.Dep>, +ls: List<&2, Line>) -> List<&2, String>:
  List.append(&2, String,
    need(Bool.or(has(ls, Dir{}), List.is_empty(&2, String, vended(ds))), rules(ls)),
    allows(ds))

# the block, where it goes: at the first allowlist line, or at the end
def placed(done: Bool, +blk: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, done, [], blk)

# every line, walked once. `fix` replaces a `.ez/` line. `blk` replaces the
# first allowlist line, every later one is dropped, and `done` says the
# block is already down; a file with no allowlist line gets it at the end.
# Every other line is kept as it was.
def walk(ls: List<&2, Line>, +fix: List<&2, String>, +blk: List<&2, String>, done: Bool) -> List<&2, String>:
  match ls:
    case []:
      placed(done, blk)
    case Line{k, +line} <> t:
      match k:
        case Other{}:
          line <> walk(t, fix, blk, done)
        case Dir{}:
          List.append(&2, String, fix, walk(t, fix, blk, done))
        case Star{}:
          line <> walk(t, fix, blk, done)
        case Lib{}:
          line <> walk(t, fix, blk, done)
        case Pkgs{}:
          line <> walk(t, fix, blk, done)
        case Allow{_h}:
          List.append(&2, String, placed(done, blk), walk(t, fix, blk, True{}))

# the walk over a file's lines, each already read for what it is
def lines.go(+ds: List<&2, M.Dep>, +ls: List<&2, Line>) -> List<&2, String>:
  walk(ls, rules(ls), block(ds, ls), False{})

# the lines of an ignore file with the allowlist the ledger's dependencies
# call for: exactly the vendored hashes, and nothing else changed
def lines(ds: List<&2, M.Dep>, ls: List<&2, String>) -> List<&2, String>:
  lines.go(ds, tag(ls))

# the text of a file less the newline it ends with, so its lines are the
# lines a person wrote and not one more empty one
def text.body(+text: String) -> String:
  Bool.pick(String, String.ends_with(text, "\n"),
    String.take(text, Nat.sub(String.length(text), 1n)), text)

# an empty file has no lines, not one empty one
def text.lines(+body: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(body), [], String.lines(body))

# a file whose lines did not change comes back byte for byte, whatever it
# ended with. One that did ends with a newline, unless nothing is left.
def text.out(same: Bool, +text: String, +out: String) -> String:
  match same:
    case True{}:
      text
    case False{}:
      Bool.pick(String, String.is_empty(out), "", out ++ "\n")

# the ignore file with the allowlist the ledger calls for. `ez add`,
# `ez remove` and `ez lock --upgrade` write this when it differs from what
# they read.
def sync(ds: List<&2, M.Dep>, +text: String) -> String:
  +kept = text.body(text)
  +out = String.join(lines(ds, text.lines(kept)), "\n")
  text.out(String.eq(out, kept), text, out)
