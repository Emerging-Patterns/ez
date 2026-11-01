# `ez add` with no ref pins the greatest semver-ish release tag on the remote;
# with no release, the greatest pre-release; with no semver-ish tag, the
# remote's default branch as its `HEAD` symref names it. A named ref resolves
# exactly, as `refs/tags/<ref>` and then `refs/heads/<ref>`. A 40-hex ref is
# used as a commit without asking the remote.
#
# What git answers is taken as given (trusted in src/git/git.bend); what ez
# decides from it is pure, and these are its laws: whether a ref is already
# a commit, the directory a package is rooted at, and which tag, branch or
# ref `ez add` pins. A tag asked of the remote as if it were a commit
# fetches nothing.
import Base
import ../src/ledger/manifest.bend as M
import ../src/git/git.bend as Git
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP

# LAW: with no ref, the tag or branch pinned is the one `Git.choose` takes
# from the remote's tags, else the branch HEAD's symref names
law add_pins_chosen:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.tag(M.source.dep(AP.added(w))) == AP.default.ref(w) : String}

# LAW: a 40-hex ref asks the remote nothing: no tags, no HEAD, no ref
law add_commit_asks_nothing:
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.wants(w)) == False{} : Bool}

# LAW: with no ref, when a tag is semver-ish, the commit pinned is the one
# the remote's tags name for the tag `Git.choose` takes, through its peeled
# row when it is annotated (`Git.exact`)
law add_pins_chosen_rev:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for c: {String.is_empty(Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))) == False{}
    : Bool}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(AP.added(w))) == Git.exact(AP.rows(w, AP.QTags{}),
    Git.choose(Git.tag.names(AP.rows(w, AP.QTags{})))) : String}

# LAW: a named ref pins the commit `Git.exact` reads for exactly that name
# from what the remote answered: the tag first, then the branch
law add_pins_named:
  for +w: A.World
  for nr: {Git.is_rev(A.ref(w)) == False{} : Bool}
  for ne: {String.is_empty(A.ref(w)) == False{} : Bool}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(AP.added(w)))
    == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}

# LAW: a 40-hex ref is pinned as the commit it is
law add_pins_commit:
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(AP.added(w))) == A.ref(w) : String}

# LAW: with no ref and no semver-ish tag among the ones the remote printed,
# the commit pinned is the one HEAD names, when its symref names a branch
law add_pins_head_rev:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for +text: String
  for t: {AP.said(w, AP.QTags{}) == Up.Said{text} : Up.Said}
  for c: {String.is_empty(Git.choose(Git.tag.names(Git.rows(String.lines(text))))) == True{}
    : Bool}
  for b: {String.is_empty(Git.tip.branch(AP.rows(w, AP.QHead{}))) == False{} : Bool}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(AP.added(w))) == Git.tip.rev(AP.rows(w, AP.QHead{})) : String}

# LAW: a ref that is not forty characters is not a commit name. A tag
# or a branch is asked of the remote.
law is_rev_needs_40:
  for +ref: String
  for e: {False{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  {Git.is_rev(ref) == False{} : Bool}

# LAW: nor is a name of the right length whose alphabet is not hex.
law is_rev_needs_hex:
  for +ref: String
  for e0: {True{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  for e1: {False{} == Git.hex.all(String.to_list(ref)) : Bool}
  {Git.is_rev(ref) == False{} : Bool}

# LAW: forty hex characters are a commit name, and need no remote.
law is_rev_hex40:
  for +ref: String
  for e0: {True{} == Nat.is_eq(String.length(ref), 40n) : Bool}
  for e1: {True{} == Git.hex.all(String.to_list(ref)) : Bool}
  {Git.is_rev(ref) == True{} : Bool}

# What `ez add` pins. With no ref named, it takes a tag chosen from every tag
# on the remote, and with no semver-ish tag, the branch HEAD's symref names.
# A named ref is looked up by its whole name. Each decision is a pure
# function over what `git ls-remote` printed, and these are its laws.

# LAW: whenever any tag is a release, the tag chosen is a release. No
# pre-release beats one, however much greater its numbers are.
law choose_release:
  for +names: List<&2, String>
  for e: {Git.has.release(names) == True{} : Bool}
  {Git.release(Git.choose(names)) == True{} : Bool}

# LAW: with no release among the tags, the choice is the greatest of them by
# the same comparator, and every semver-ish one of them is a pre-release
law choose_prerelease:
  for +names: List<&2, String>
  for e: {Git.has.release(names) == False{} : Bool}
  {Git.choose(names) == Git.latest(names) : String}

# LAW: the default branch is the one HEAD's symref row names
law branch_of_symref:
  for +b: String
  for rest: List<&2, Git.Row>
  for e: {False{} == String.is_empty(b) : Bool}
  {Git.tip.branch(Git.Row{"ref: refs/heads/" ++ b, "HEAD"} <> rest) == b : String}

# LAW: a row that is not HEAD's says nothing about the default branch
law branch_skips_other:
  for rev: String
  for +name: String
  for rest: List<&2, Git.Row>
  for e: {False{} == String.eq(name, "HEAD") : Bool}
  {Git.tip.branch(Git.Row{rev, name} <> rest) == Git.tip.branch(rest) : String}

# LAW: nor does HEAD's commit row, which is not a symref
law branch_skips_commit:
  for +rev: String
  for rest: List<&2, Git.Row>
  for e: {False{} == String.starts_with(rev, "ref: ") : Bool}
  {Git.tip.branch(Git.Row{rev, "HEAD"} <> rest) == Git.tip.branch(rest) : String}

# LAW: a row whose ref name is not exactly `refs/tags/<ref>`, its peeled
# `^{}` form, or `refs/heads/<ref>` is never picked: taking it away changes
# nothing. `refs/heads/feature/main` is such a row for `main`.
law exact_skips:
  for rev: String
  for +name: String
  for +rs: List<&2, Git.Row>
  for +ref: String
  for e0: {False{} == String.eq(name, "refs/tags/" ++ ref ++ "^{}") : Bool}
  for e1: {False{} == String.eq(name, "refs/tags/" ++ ref) : Bool}
  for e2: {False{} == String.eq(name, "refs/heads/" ++ ref) : Bool}
  {Git.exact(Git.Row{rev, name} <> rs, ref) == Git.exact(rs, ref) : String}

# LAW: a tag the remote has is the answer, whatever branch shares its name
law exact_tag_first:
  for +rs: List<&2, Git.Row>
  for +ref: String
  for e: {False{} == String.is_empty(Git.named(rs, "refs/tags/" ++ ref)) : Bool}
  {Git.exact(rs, ref) == Git.or_else(Git.named(rs, "refs/tags/" ++ ref ++ "^{}"),
    Git.named(rs, "refs/tags/" ++ ref)) : String}

# LAW: a branch is the answer only when no tag of that name is
law exact_branch:
  for +rs: List<&2, Git.Row>
  for +ref: String
  for e0: {"" == Git.named(rs, "refs/tags/" ++ ref ++ "^{}") : String}
  for e1: {"" == Git.named(rs, "refs/tags/" ++ ref) : String}
  {Git.exact(rs, ref) == Git.named(rs, "refs/heads/" ++ ref) : String}

# Which tag is greatest. Each law takes the tags as any list with one tag
# `n` somewhere in it, `xs ++ [n] ++ ys`, so it speaks of every tag in every
# list. "Greater" is `Git.newer` of `Git.ord.ver`, the comparator the folds
# use: numeric parts compare as numbers, missing parts pad with zero, and a
# pre-release compares by semver's rules below the release it precedes.

# LAW: no semver-ish tag is newer than the one `latest` answers
law latest_greatest:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +ns: List<&2, Nat>
  for +ps: List<&2, Git.Id>
  for +ev: {Git.ver.of(n) == Git.Yes{ns, ps} : Git.Ver}
  {Git.newer(Git.ord.ver(Git.ver.of(n),
    Git.ver.of(Git.latest(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: no release is newer than the one `latest.rel` answers
law latest_rel_greatest:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +e: {Git.release(n) == True{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n),
    Git.ver.of(Git.latest.rel(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: the tag `ez add` pins is the greatest release: no release on the
# remote is newer, and with `choose_release` it is itself a release
law choose_greatest_release:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +e: {Git.release(n) == True{} : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n),
    Git.ver.of(Git.choose(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: with no release on the remote, the tag `ez add` pins is the greatest
# pre-release: no semver-ish tag is newer
law choose_greatest_prerelease:
  for +xs: List<&2, String>
  for +n: String
  for +ys: List<&2, String>
  for +ns: List<&2, Nat>
  for +ps: List<&2, Git.Id>
  for +ev: {Git.ver.of(n) == Git.Yes{ns, ps} : Git.Ver}
  for +e: {Git.has.release(List.append(&2, String, xs, n <> ys)) == False{}
    : Bool}
  {Git.newer(Git.ord.ver(Git.ver.of(n),
    Git.ver.of(Git.choose(List.append(&2, String, xs, n <> ys))))) == False{}
    : Bool}

# LAW: and the tag it pins, when it pins one, is one of the remote's tags
law choose_is_a_tag:
  for +names: List<&2, String>
  for e: {String.is_empty(Git.choose(names)) == False{} : Bool}
  exs xs: List<&2, String>
  exs ys: List<&2, String>
  {List.append(&2, String, xs, Git.choose(names) <> ys) == names
    : List<&2, String>}
