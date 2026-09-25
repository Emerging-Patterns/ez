# add: the laws. The human states them; PROOF.bend must prove them. They are
# stated over the plan `ez add` runs (`AP.command`) and the questions it
# asks (`AP.next`), so what they say of the plan is what the command does,
# the interpreter's faithfulness being EZ-TRUST-2.
#
# `AP.command` is the git planner's plan (`AP.plan`) for a git or path
# target and the hub planner's (`H.plan`, add/hub.bend) for a hub package's
# `<name>@<version>` (`add_runs_plan`, `add_runs_hub`). The laws of the first
# part are stated over the command; those after them over the planner that
# runs.
#
# `AP.added(w)` is the dependency the git plan records and `H.added(w)` the
# one the hub plan records: every law about them holds of every World, and
# `add_edits_ledger` and `add_named_edits_ledger` say an add that does not
# refuse writes exactly it into ez.toml, through `Rend.add.keep`.
import Base
import ./world.bend as A
import ./plan.bend as AP
import ./hub.bend as H
import ../lock/plan.bend as P
import ../lock/up.bend as Up
import ../lock/world.bend as W
import ../lock/lock.bend as L
import ../hub/hub.bend as Web
import ../ledger/manifest.bend as M
import ../ledger/LAWS.bend as ML
import ../ledger/render.bend as Rend
import ../ledger/ignore.bend as I
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as Git
import ../ez/target.bend as Tgt
import ../ez/named.bend as Named

# LAW: `ez add` that refuses writes, lays and removes nothing: not ez.toml,
# not `.gitignore`, no tree under BEND_LIB or `.ez/lib`, no name's file. Its
# plan has no effect at all; the reason is how it ends. So a refused add
# fills no cache either.
# EZ-OUT-2
law add_refusal_writes_nothing:
  for +w: A.World
  for r: {AP.refuses.command(w) == True{} : Bool}
  {P.writes(AP.command(w)) == False{} : Bool}

# LAW: `ez add` ends with the status of its plan's outcome, which is 1
# exactly when it refuses and 0 when it does not
# EZ-OUT-1
law add_exits_as_it_refuses:
  for +w: A.World
  {P.code(AP.command(w)) == P.status.of(AP.refuses.command(w)) : U32}

# LAW: with no ez.toml, `ez add` refuses, whatever it was asked to add, a
# hub package's name included
# EZ-LED-6
law add_needs_ledger:
  for +a: A.Args
  for +here: String
  for +home: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  {AP.refuses.command(A.World{a, here, home, None{}, ignore, rs, hs}) == True{} : Bool}

# LAW: and asks nothing first, of a remote or of the hub
# EZ-LED-6
law add_needs_ledger_asks_nothing:
  for +a: A.Args
  for +here: String
  for +home: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  {AP.next.asks(AP.next(A.World{a, here, home, None{}, ignore, rs, hs})) == False{} : Bool}

# LAW: a ledger that does not parse is refused, so `ez add` writes no guess
# over it
# EZ-LED-1
law add_refuses_unread:
  for +a: A.Args
  for +here: String
  for +home: String
  for +s: String
  for +ignore: String
  for +rs: List<&2, Up.Reply>
  for +hs: List<&2, W.Reply>
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {AP.refuses.command(A.World{a, here, home, Some{s}, ignore, rs, hs}) == True{} : Bool}

# LAW: a target that is not a hub package's name runs the git planner
law add_runs_plan:
  for +w: A.World
  for g: {A.named(w) == False{} : Bool}
  {AP.command(w) == AP.plan(w) : P.Plan}

# LAW: and one that is runs the hub planner
law add_runs_hub:
  for +w: A.World
  for n: {A.named(w) == True{} : Bool}
  {AP.command(w) == H.plan(w) : P.Plan}

# ---------------------------------------------------------------------------
# a git or path target (`AP.plan`)

# LAW: `ez add` that does not refuse writes to ez.toml exactly the ledger
# `Rend.add.keep` gives with the dependency it records, the edit
# `add_keep_idem` says is the same done twice
# EZ-LED-2
law add_edits_ledger:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  {P.put.plan(AP.plan(w), "ez.toml")
    == P.Put{Rend.show(Rend.add.keep(m, AP.added(w)))} : P.Wrote}

# LAW: and the ledger it writes there reads back as that ledger. A ledger
# that could not be written so that it reads back is refused, with no effect.
# EZ-LED-4
law add_ledger_reads_back:
  for +w: A.World
  for +m: M.Manifest
  for +good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  for +text: String
  for put: {P.put.plan(AP.plan(w), "ez.toml") == P.Put{text} : P.Wrote}
  for rb: ML.ReadsBack()
  {M.parse(text) == M.Good{Rend.add.keep(m, AP.added(w))} : M.Read}

# LAW: and leaves `.gitignore` holding exactly the file `I.sync` derives from
# the dependencies of that ledger: written when that changes it, kept as it
# was when it does not. `allowlist_is_the_ledger` and
# `allowlist_keeps_other_lines` say what that file's lines are.
# EZ-VEN-1
law add_syncs_allowlist:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.after(P.put.plan(AP.plan(w), ".gitignore"), A.ignore(w))
    == I.sync(A.deps.of(Rend.add.keep(m, AP.added(w))), A.ignore(w)) : String}

# LAW: the dependency is recorded under the name `Named.as` gives, over the
# ledger, the source, `--rename`, and the checkout's own `[package] name`
# EZ-LED-7
law add_records_named:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.dep.name(AP.added(w))
    == Named.as(A.deps(w), A.url(w), A.rename(w), AP.pkg(w), A.fresh(w)) : String}

# LAW: and whenever `Named.why.as` objects to that name, `ez add` refuses
# EZ-LED-7
law add_refuses_named:
  for +w: A.World
  for why: {False{} == String.is_empty(Named.why.as(A.deps(w), AP.name(w), A.url(w),
    A.rename(w))) : Bool}
  {AP.refuses(w) == True{} : Bool}

# LAW: the source recorded is the target as it was given: a URL as it is, a
# path with a leading `~/` expanded (`add_path_as_given`)
# EZ-LED-8
law add_records_as_given:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.url(M.source.dep(AP.added(w))) == A.url(w) : String}

# LAW: a path target is that path, with only `~` expanded against HOME: a
# relative one stays relative to the project
# EZ-LED-8
law add_path_as_given:
  for +w: A.World
  for +p: String
  for e: {Tgt.classify(A.target(w)) == Tgt.Local{p} : Tgt.Place}
  {A.url(w) == Tgt.expand(A.home(w), p) : String}

# LAW: every question `ez add` asks git names the source anchored where ez
# runs, which is the project root, so a relative path resolves against it
# EZ-LED-8
law add_asks_anchored:
  for +w: A.World
  {AP.asks.from(AP.wants(w), Path.anchor(A.here(w), A.url(w))) == True{} : Bool}

# LAW: with no ref, the tag or branch pinned is the one `Git.choose` takes
# from the remote's tags, else the branch HEAD's symref names
# EZ-RES-1
law add_pins_chosen:
  for +w: A.World
  for none: {A.ref(w) == "" : String}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.tag(M.source.dep(AP.added(w))) == AP.default.ref(w) : String}

# LAW: a 40-hex ref asks the remote nothing: no tags, no HEAD, no ref
# EZ-RES-1
law add_commit_asks_nothing:
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  {AP.resolves(AP.wants(w)) == False{} : Bool}

# LAW: with no entry, the one walked and recorded is the checkout's
# `[package] entry`, else its `bin`, else `main.bend` (`Git.entry.maybe`)
# EZ-RES-2
law add_entry_default:
  for +w: A.World
  for none: {A.entry.arg(w) == "" : String}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.dep.entry(AP.added(w)) == Git.entry.maybe(K.look(AP.files(w), "ez.toml")) : String}

# LAW: an entry the checkout does not hold is refused, never hashed as an
# empty package
# EZ-RES-2
law add_entry_absent:
  for +w: A.World
  for miss: {None{} == K.look(AP.files(w), Path.norm(AP.entry(w))) : Maybe<&2, String>}
  {AP.refuses(w) == True{} : Bool}

# LAW: `ez add` that does not refuse ends what it says with the import line
# for the entry's path inside the package it walked, which is where the hub
# serves the entry: its name alone, or, when an import climbs out of its
# directory, the entry under the directories the package re-rooted above it.
# `Git.import.line` is the line `ez publish` prints for a package too.
# EZ-RES-2
law add_says_import:
  for +w: A.World
  for +ok: {AP.refuses(w) == False{} : Bool}
  {AP.last(AP.plan(w)) == Git.import.line(AP.hash(w), AP.at(w)) : String}

# LAW: a walk that refuses, such as one whose imports climb out of the
# checkout, refuses the add
law add_walk_refused:
  for +w: A.World
  for +why: String
  for e: {AP.walked(w) == K.Refused{why} : K.Walked}
  {AP.refuses(w) == True{} : Bool}

# LAW: every tree `ez add` lays is named by the manifest of the texts it
# lays: its last file is the manifest of the others, each weighed by its own
# text, and its hash is that manifest's `0x` name
# EZ-HASH-3
law add_lays_named:
  for +w: A.World
  {P.lays.named(P.effects(AP.plan(w))) == True{} : Bool}

# LAW: with no ref, when a tag is semver-ish, the commit pinned is the one
# the remote's tags name for the tag `Git.choose` takes, through its peeled
# row when it is annotated (`Git.exact`)
# EZ-RES-1
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
# EZ-RES-1
law add_pins_named:
  for +w: A.World
  for nr: {Git.is_rev(A.ref(w)) == False{} : Bool}
  for ne: {String.is_empty(A.ref(w)) == False{} : Bool}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(AP.added(w)))
    == Git.exact(AP.rows(w, AP.QRefs{A.ref(w)}), A.ref(w)) : String}

# LAW: a 40-hex ref is pinned as the commit it is
# EZ-RES-1
law add_pins_commit:
  for +w: A.World
  for hex: {Git.is_rev(A.ref(w)) == True{} : Bool}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.source.rev(M.source.dep(AP.added(w))) == A.ref(w) : String}

# LAW: with no ref and no semver-ish tag among the ones the remote printed,
# the commit pinned is the one HEAD names, when its symref names a branch
# EZ-RES-1
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

# LAW: `ez add` records the dependency among the dependencies and keeps the
# ledger's `[tools.*]` pins as they were: the ledger it writes has the tools
# it read, and its dependencies are the ones it read with the one added
# EZ-LED-5
law add_keeps_tools:
  for +w: A.World
  for +n: String
  for +e: String
  for +b: String
  for +h: String
  for +hpa: String
  for +hpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for good: {A.read(w) == M.Good{M.Manifest{n, e, b, h, hpa, hpv, ds, ts}} : M.Read}
  for +ok: {AP.refuses(w) == False{} : Bool}
  {P.put.plan(AP.plan(w), "ez.toml")
    == P.Put{Rend.show(M.Manifest{n, e, b, h, hpa, hpv,
      List.append(&2, M.Dep, Rend.without(ds, M.dep.name(Rend.readd(ds, AP.added(w)))),
        [Rend.readd(ds, AP.added(w))]), ts})} : P.Wrote}

# ---------------------------------------------------------------------------
# a hub package's `<name>@<version>` (`H.plan`)

# LAW: `ez add <name>@<version>` that refuses writes, lays and removes
# nothing
# EZ-OUT-2
law add_named_refusal_writes_nothing:
  for +w: A.World
  for r: {H.refuses(w) == True{} : Bool}
  {P.writes(H.plan(w)) == False{} : Bool}

# LAW: a name the hub has no package for is refused
# EZ-OUT-2
law add_named_refuses_unknown:
  for +w: A.World
  for why: String
  for miss: {H.heard(A.hubs(w), A.target(w)) == Some{W.Miss{why}} : Maybe<&2, W.Answer>}
  {H.refuses(w) == True{} : Bool}

# LAW: and so is one it answers with anything but a `0x` name
# EZ-OUT-2
law add_named_refuses_unhashed:
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  for bad: {L.hash.ok(String.trim(text)) == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: a package whose manifest does not hash to the name the hub answered
# is refused, never laid or recorded
# EZ-OUT-2
law add_named_refuses_manifest:
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  for how: W.How
  for +manifest: String
  for ss: List<&2, String>
  for got: {H.heard(A.hubs(w), String.trim(text)) == Some{W.Got{how, manifest, ss}}
    : Maybe<&2, W.Answer>}
  for bad: {Web.matches(L.want(String.trim(text)), manifest) == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: the key is `--rename` when given, else the key the ledger gives a
# dependency added by the same name part, else the name part itself
# EZ-LED-7
law add_named_key:
  for +w: A.World
  {M.dep.name(H.added(w))
    == Named.hub.key(A.deps(w), Named.hub.part(A.target(w)), A.rename(w)) : String}

# LAW: and whenever `Named.hub.why` objects to it, the add refuses: a
# `--rename` that is no key, one of a name the ledger records under another
# key, or a key the ledger gives another dependency
# EZ-LED-7
law add_named_refuses_clash:
  for +w: A.World
  for why: {False{} == String.is_empty(Named.hub.why(A.deps(w), H.key(w), H.part(w),
    A.rename(w))) : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: a ledger that could not be written so that it reads back is refused
# EZ-LED-4
law add_named_refuses_unrenderable:
  for +w: A.World
  for bad: {Rend.renderable(Rend.add.keep(A.manifest.of(A.read(w)), H.added(w)))
    == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: an add that does not refuse writes to ez.toml exactly the ledger
# `Rend.add.keep` gives with the dependency it records
# EZ-LED-2
law add_named_edits_ledger:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {H.refuses(w) == False{} : Bool}
  {P.put.plan(H.plan(w), "ez.toml")
    == P.Put{Rend.show(Rend.add.keep(m, H.added(w)))} : P.Wrote}

# LAW: and that ledger reads back as itself
# EZ-LED-4
law add_named_reads_back:
  for +w: A.World
  for +m: M.Manifest
  for +good: {A.read(w) == M.Good{m} : M.Read}
  for +ok: {H.refuses(w) == False{} : Bool}
  for +text: String
  for put: {P.put.plan(H.plan(w), "ez.toml") == P.Put{text} : P.Wrote}
  for rb: ML.ReadsBack()
  {M.parse(text) == M.Good{Rend.add.keep(m, H.added(w))} : M.Read}

# LAW: the dependency recorded is the name as it was given, under `hub`,
# with the hash the hub answered for it, so the ledger names that name to
# that hash, and the next `ez lock` reads the pair from the ledger without
# asking the hub (EZ-HUB-2)
# EZ-HUB-1
law add_named_records_name:
  for +w: A.World
  for +text: String
  for said: {H.heard(A.hubs(w), A.target(w)) == Some{W.Said{text}} : Maybe<&2, W.Answer>}
  for +ok: {H.refuses(w) == False{} : Bool}
  {H.added(w) == M.Dep{H.key(w), String.trim(text), M.dep.entry(H.added(w)),
    M.Hub{A.target(w)}} : M.Dep}

# LAW: an add that does not refuse lays the name's file,
# `$BEND_LIB/names/<name>@<version>`, holding the hash it records, and no
# other, so bend reads the name without asking the hub
# EZ-HUB-4
law add_named_lays_name:
  for +w: A.World
  for +ok: {H.refuses(w) == False{} : Bool}
  {H.names.laid(P.effects(H.plan(w))) == [L.Name{A.target(w), M.dep.hash(H.added(w))}]
    : List<&2, L.Name>}

# LAW: every tree the add lays is named by the manifest of the texts it
# lays, and its hash is that manifest's `0x` name
# EZ-HASH-3
law add_named_lays_named:
  for +w: A.World
  {P.lays.named(P.effects(H.plan(w))) == True{} : Bool}

# LAW: with no entry given, the one recorded is the package's `main.bend`,
# else its first top-level `.bend` file, else none
# EZ-RES-2
law add_named_entry_default:
  for +w: A.World
  for ne: {A.entry.arg(w) == "" : String}
  for nr: {A.ref(w) == "" : String}
  {M.dep.entry(H.added(w)) == H.entry.of(H.files(w)) : String}

# LAW: an entry given that the package does not hold is refused
# EZ-RES-2
law add_named_entry_absent:
  for +w: A.World
  for given: {String.is_empty(H.asked(w)) == False{} : Bool}
  for miss: {H.holds(H.files(w), Path.norm(H.asked(w))) == False{} : Bool}
  {H.refuses(w) == True{} : Bool}

# LAW: an add that does not refuse and records an entry ends what it says
# with the import line for that entry by name, the line `ez publish` prints
# with the name in place of the hash
# EZ-RES-2
law add_named_says_import:
  for +w: A.World
  for +ok: {H.refuses(w) == False{} : Bool}
  for some: {String.is_empty(M.dep.entry(H.added(w))) == False{} : Bool}
  {H.last(H.plan(w)) == Git.import.line(A.target(w), Path.norm(M.dep.entry(H.added(w))))
    : String}

# LAW: every question the add asks names the hub the ledger names
# EZ-HUB-1
law add_named_asks_hub:
  for +w: A.World
  {H.asks.hub(H.wants(w), A.hub(w)) == True{} : Bool}
