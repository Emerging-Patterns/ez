# A dependency's ledger name is `--rename` when given, which must be a TOML
# bare key; otherwise the name the ledger already records for that source;
# otherwise the target's `[package] name` when it is a TOML bare key;
# otherwise the repository's name; otherwise the directory's name. A hub
# package added by its `<name>@<version>` is named by `--rename` when given;
# otherwise by the name the ledger already records for a dependency added by
# the same name part, so another version replaces it; otherwise by the name
# part. A name the ledger gives a different source is refused, and so is a
# `--rename` of a source the ledger records under another name.
import Base
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../src/ez/named.bend as Named

# LAW: the dependency is recorded under the name `Named.as` gives, over the
# ledger, the source, `--rename`, and the checkout's own `[package] name`
law add_records_named:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.dep.name(AP.added(w))
    == Named.as(A.deps(w), A.url(w), A.rename(w), AP.pkg(w), A.fresh(w)) : String}

# LAW: and whenever `Named.why.as` objects to that name, `ez add` refuses
law add_refuses_named:
  for +w: A.World
  for why: {False{} == String.is_empty(Named.why.as(A.deps(w), AP.name(w), A.url(w),
    A.rename(w))) : Bool}
  {AP.refuses(w) == True{} : Bool}

# LAW: the key is `--rename` when given, else the key the ledger gives a
# dependency added by the same name part, else the name part itself
law add_named_key:
  for +w: A.World
  {M.dep.name(H.added(w))
    == Named.hub.key(A.deps(w), Named.hub.part(A.target(w)), A.rename(w)) : String}

# LAW: and whenever `Named.hub.why` objects to it, the add refuses: a
# `--rename` that is no key, one of a name the ledger records under another
# key, or a key the ledger gives another dependency
law add_named_refuses_clash:
  for +w: A.World
  for why: {False{} == String.is_empty(Named.hub.why(A.deps(w), H.key(w), H.part(w),
    A.rename(w))) : Bool}
  {H.refuses(w) == True{} : Bool}

# named: what `ez add` records a dependency under. Its source names it, never
# its entry file; the ledger keeps the name it already gave that source, and
# refuses to hand a name it gave one source to another.

# LAW: a source is named by what follows its last slash, whatever comes
# before. A slug, a url and a resolved directory are all named this way, so
# two packages whose entry is `main.bend` are named after their repositories.
law leaf_is_last:
  for p: String
  for +n: String
  for e: {Named.Seen{False{}, n} == Named.last(n) : Named.Seen}
  {Named.leaf(p ++ ("/" ++ n)) == n : String}

# LAW: a package whose own `[package] name` is a TOML bare key is named by it
law own_package:
  for +pkg: String
  for +fresh: String
  for e: {True{} == Named.bare(pkg) : Bool}
  {Named.own(pkg, fresh) == pkg : String}

# LAW: a package name that is not a bare key, or none at all, falls through to
# the name the source gives itself rather than being refused
law own_invalid:
  for +pkg: String
  for +fresh: String
  for e: {False{} == Named.bare(pkg) : Bool}
  {Named.own(pkg, fresh) == fresh : String}

# LAW: the name the ledger already gives this source beats the package's own
# name and the source's
law name_keeps:
  for n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for +pkg: String
  for +fresh: String
  {Named.name(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    pkg, fresh) == n : String}

# LAW: `--rename`, when given, is the name, ahead of the ledger's, the
# package's and the source's
law rename_wins:
  for ds: List<&2, M.Dep>
  for +url: String
  for +rename: String
  for +pkg: String
  for +fresh: String
  for e: {False{} == String.is_empty(rename) : Bool}
  {Named.as(ds, url, rename, pkg, fresh) == rename : String}

# LAW: a `--rename` that is not a bare key, like `a.b`, is refused
law rename_dotted:
  for +a: String
  for +b: String
  {Named.renamed.ok(a ++ ("." ++ b)) == False{} : Bool}

# LAW: a `--rename` of a source the ledger already records under another name
# is refused, rather than recorded twice or renamed behind the ledger's back
law rename_moved:
  for +n: String
  for +h: String
  for +en: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +t: List<&2, M.Dep>
  for +rename: String
  for er: {False{} == String.is_empty(rename) : Bool}
  for en0: {False{} == String.is_empty(n) : Bool}
  for nr: {False{} == String.eq(n, rename) : Bool}
  {Named.moved(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, url,
    rename) == True{} : Bool}

# LAW: and a `--rename` the ledger gives to another source still clashes
law rename_clash:
  for +r: String
  for +h: String
  for +en: String
  for +u: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for +vend: Bool
  for +t: List<&2, M.Dep>
  for +pkg: String
  for +fresh: String
  for ne: {False{} == String.eq(u, url) : Bool}
  for er: {False{} == String.is_empty(r) : Bool}
  {Named.clash(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t,
    Named.as(M.Dep{r, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, url, r,
      pkg, fresh), url) == True{} : Bool}

# LAW: the name held by this same git source is not a clash: that is a re-add
law clash_same:
  for +n: String
  for h: String
  for en: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  {Named.clash(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, n,
    url) == False{} : Bool}

# LAW: the name held by another git source is a clash, and is refused rather
# than written over
law clash_other:
  for +n: String
  for h: String
  for en: String
  for u: String
  for +url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for ne: {False{} == String.eq(u, url) : Bool}
  {Named.clash(M.Dep{n, h, en, M.Git{u, rev, tag, root, nar, vend}} <> t, n,
    url) == True{} : Bool}

# LAW: and so is the name held by a hub dependency
law clash_hub:
  for +n: String
  for h: String
  for en: String
  for +url: String
  for t: List<&2, M.Dep>
  {Named.clash(M.Dep{n, h, en, M.Hub{""}} <> t, n, url) == True{} : Bool}

# LAW: a hub package is recorded under `--rename` when it is given
law hub_rename_wins:
  for ds: List<&2, M.Dep>
  for +part: String
  for +rename: String
  for e: {False{} == String.is_empty(rename) : Bool}
  {Named.hub.key(ds, part, rename) == rename : String}

# LAW: else under the key the ledger gives a dependency added by the same
# name part, so another version replaces it, as a git dependency added again
# at a new tag does
law hub_key_keeps:
  for +n: String
  for h: String
  for en: String
  for +nv: String
  for t: List<&2, M.Dep>
  for e: {False{} == String.is_empty(n) : Bool}
  {Named.hub.key(M.Dep{n, h, en, M.Hub{nv}} <> t, Named.hub.part(nv), "") == n : String}

# LAW: else under the name part itself
law hub_key_fresh:
  for +part: String
  {Named.hub.key([], part, "") == part : String}

# LAW: a key the ledger gives a git dependency clashes
law hub_clash_git:
  for +k: String
  for h: String
  for en: String
  for url: String
  for rev: String
  for tag: String
  for root: String
  for nar: String
  for vend: Bool
  for t: List<&2, M.Dep>
  for +part: String
  {Named.hub.clash(M.Dep{k, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, k, part)
    == True{} : Bool}
