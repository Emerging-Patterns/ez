# manifest/upgrade: what `ez lock --upgrade` may do to one dependency, before
# it talks to a remote. The ledger pins exact commits. A tag is the only
# floating name a person wrote down, so that is what gets re-resolved. A pin
# with no tag fast-forwards to the default branch tip when the commit is an
# ancestor of it, and stays a commit pin. A hub package is the hash itself.
# `vend` says the tree under `.ez/lib/<hash>` is committed, so a move lays the
# new tree there; the allowlist that names it is `manifest/ignore.bend`'s,
# derived from the ledger the move writes. A move also rewrites an
# `import 0x<hash>` line that names the old hash.
import Base
import ./manifest.bend as M

# what an upgrade will ask the remote, once the ledger has been read
type Aim is Data:
  Hold{}
  Follow{+ref: String}
  Forward{}

# what that answer means for the pin
type Verdict is Data:
  Keep{}
  Drift{}
  Off{}
  Advance{rev: String, tag: String}

# one hash that moved, and the hash that replaces it: an import line to
# rewrite, or a committed tree to remove
type Swap is Data:
  Swap{old: String, new: String}

# an empty `--package` is every dependency; a name is that one
def chosen.go(all: Bool, +only: String, +name: String) -> Bool:
  match all:
    case True{}:
      True{}
    case False{}:
      String.eq(only, name)

# an empty `--package` is every dependency; a name is that one
def chosen(+only: String, +name: String) -> Bool:
  chosen.go(String.is_empty(only), only, name)

# the rest of the scan only when this one was not it
def known.step(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether the ledger names this dependency
def known.in(ds: List<&2, M.Dep>, +name: String) -> Bool:
  match ds:
    case []:
      False{}
    case +h <> t:
      known.step(String.eq(M.dep.name(h), name), _u => known.in(t, name))

# `--package` with no such dependency is a mistake, and no filter is not
def known.go(all: Bool, ds: List<&2, M.Dep>, +name: String) -> Bool:
  match all:
    case True{}:
      True{}
    case False{}:
      known.in(ds, name)

# whether the ledger names the dependency `--package` asked for
def known(+only: String, ds: List<&2, M.Dep>) -> Bool:
  known.go(String.is_empty(only), ds, only)

# a selected git pin with no tag follows the default branch
def aim.tag(bare: Bool, +tag: String) -> Aim:
  match bare:
    case True{}:
      Forward{}
    case False{}:
      Follow{tag}

# a selected hub pin has nothing to follow
def aim.src(source: M.Source) -> Aim:
  match source:
    case M.Hub{}:
      Hold{}
    case M.Git{_url, _rev, +tag, _root, _nar, _vend}:
      aim.tag(String.is_empty(tag), tag)

# what this dependency is asked. Unselected dependencies are left alone,
# including a git one, so `--package` does not move its neighbours.
def aim(sel: Bool, source: M.Source) -> Aim:
  match sel:
    case False{}:
      Hold{}
    case True{}:
      aim.src(source)

# the same commit either still hashes to the pin or it does not
def judge.same(agree: Bool) -> Verdict:
  match agree:
    case True{}:
      Keep{}
    case False{}:
      Drift{}

# a different commit is the upgrade only when it descends from the pin
def judge.move(onward: Bool, +rev: String, +tag: String) -> Verdict:
  match onward:
    case True{}:
      Advance{rev, tag}
    case False{}:
      Off{}

# `same` is the resolved commit against the pin. `onward` is that commit
# being a descendant of the pin. `agree` is the recomputed hash, NAR hash
# and root against what the ledger recorded, and it only matters when the
# commit did not move.
def judge(same: Bool, onward: Bool, agree: Bool, rev: String, tag: String) -> Verdict:
  match same:
    case True{}:
      judge.same(agree)
    case False{}:
      judge.move(onward, rev, tag)

# the three fields a checkout can disagree on, each required
def agree.nar(same_nar: Bool, same_root: Bool) -> Bool:
  match same_nar:
    case False{}:
      False{}
    case True{}:
      same_root

# whether a recomputed pin is the one the ledger already recorded
def agree.go(same_hash: Bool, same_nar: Bool, same_root: Bool) -> Bool:
  match same_hash:
    case False{}:
      False{}
    case True{}:
      agree.nar(same_nar, same_root)

# whether a recomputed pin is the one the ledger already recorded
def agree(+oh: String, +nh: String, +onar: String, +nnar: String, +oroot: String, +nroot: String) -> Bool:
  agree.go(String.eq(oh, nh), String.eq(onar, nnar), String.eq(oroot, nroot))

# a hub miss is a different digest only when the body arrived and hashed
# wrong. A package the hub has never seen is not that.
def hub.bad(+why: String) -> Bool:
  String.contains(why, "does not hash")

# the dependency with a new commit written in, and the name, the entry, the
# tag and the vendor bit left as they were
def retarget.go(
  +name: String,
  +entry: String,
  source: M.Source,
  +rev: String,
  +hash: String,
  +root: String,
  +nar: String
) -> M.Dep:
  match source:
    case M.Hub{}:
      M.Dep{name, hash, entry, M.Hub{}}
    case M.Git{url, _rev, tag, _root, _nar, vend}:
      M.Dep{name, hash, entry, M.Git{url, rev, tag, root, nar, vend}}

# the dependency with a new commit written in
def retarget(dep: M.Dep, +rev: String, +hash: String, +root: String, +nar: String) -> M.Dep:
  M.Dep{n, _h, e, s} = dep
  retarget.go(n, e, s, rev, hash, root, nar)

# the first of a list of strings, or ""
def reimport.head(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case h <> _t:
      h

# the package hash an import line names, or "" when the line names none.
# `import 0x<hash>/<file>.bend as P` is the only shape bend has.
def reimport.hash.go(named: Bool, +line: String) -> String:
  match named:
    case True{}:
      reimport.head(String.split(String.drop(line, 7n), '/'))
    case False{}:
      ""

def reimport.hash(+line: String) -> String:
  reimport.hash.go(String.starts_with(line, "import 0x"), line)

# an empty hash matches every line that names none, so it rewrites nothing
def reimport.hit(empty: Bool, +line: String, +old: String) -> Bool:
  match empty:
    case True{}:
      False{}
    case False{}:
      String.eq(reimport.hash(line), old)

# one line, with the branch already chosen. A match cannot scrutinise a call.
def reimport.line.go(hit: Bool, +line: String, +old: String, +new: String) -> String:
  match hit:
    case True{}:
      "import " ++ new ++ String.drop(line, Nat.add(7n, String.length(old)))
    case False{}:
      line

# one line, with its import hash rewritten when the line names the old one
def reimport.line(+line: String, +old: String, +new: String) -> String:
  reimport.line.go(reimport.hit(String.is_empty(old), line, old), line, old, new)

# every line, in order
def reimport.lines(ls: List<&2, String>, +old: String, +new: String) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      reimport.line(h, old, new) <> reimport.lines(t, old, new)

# a source file with one import hash replaced by another. A line that does
# not name it is left as it was, including the newline `String.lines` keeps.
def reimport(+text: String, +old: String, +new: String) -> String:
  String.join(reimport.lines(String.lines(text), old, new), "\n")

# every replacement, in order
def reimport.many(ss: List<&2, Swap>, +text: String) -> String:
  match ss:
    case []:
      text
    case Swap{+old, +new} <> t:
      reimport.many(t, reimport(text, old, new))
