# Design: workspaces

## Draft Status

State: Accepted. Nothing here changes ez yet. The rows are in `SPEC.md` as EZ-WS-1 to EZ-WS-9, all pending, and the work packages below land them.

This is the design for workspaces in the style of uv's: one repository holding several ez packages, sharing one lock, one `BEND_LIB` and one pin per git source, where one package can depend on another in the same repository. It follows the planner pattern of [ez-lock-planner.md](ez-lock-planner.md) and [ez-add-planner.md](ez-add-planner.md): every decision below is a pure function a law can reach, and the interpreter gains only the reads it needs to answer new questions.

### Open questions

Every question below was the maintainer's, and each is resolved. The maintainer accepted every recommendation.

- [x] <!-- REVIEW (resolved): One pin per git source is checked across the members' own ledgers, as uv checks one resolution across members' pyproject files, rather than kept in a root `[workspace.deps]` table as cargo keeps `[workspace.dependencies]`. We recommend uv's shape: a member's ledger stays a complete ledger, and `ez add` in a member needs no new syntax. -->
- [x] <!-- REVIEW (resolved): A plain `ez lock` refuses when a member imported by hash has moved, and the import rewrite is left to `ez lock --upgrade --package`. We recommend this, because it keeps a plain lock from writing any source, which is how a moved git dependency works today. The other choice, a plain lock that rewrites, makes the loop shorter but makes `ez lock` an editor of source files. -->
- [x] <!-- REVIEW (resolved): EZ-HUB-1 and EZ-HUB-2 are reworded so that a name a member is published as resolves to that member first (see "Named members"). Both rows are proved, so this is a behavior change to a released guarantee, though nothing changes for a project that is not a workspace. -->

---

## Summary

A repository like this one becomes a workspace by giving its root ledger a `[workspace]` table:

```toml
[package]
name = "app"
entry = "main.bend"
[workspace]
members = ["cli", "libs/*"]
exclude = ["libs/scratch"]
[deps]
[deps.parse]
workspace = true
```

Each member is a directory with its own ez.toml. `ez lock` run anywhere in the workspace writes one `ez.lock.toml` at the root. `ez fetch` lays every package into the root's `BEND_LIB`. A member depends on another member with `workspace = true`, and imports it the way it would import that package from the hub: by name when it has a published name, by hash when it does not.

## Members (EZ-WS-1)

`members` lists directories relative to the root. An entry is a plain path, or `<dir>/*`, which names every directory directly under `<dir>` that holds a committed ez.toml. That is the one glob form. uv takes full globs, but every workspace we have seen uses either a list or one `packages/*`, and a single form is easy to state exactly and to prove. `exclude` takes plain paths and removes them from the set. A directory is a member once however many entries name it, since the set is the ledgers git lists, each kept or not; the lock's own order comes from EZ-DOC-2, so nothing depends on the order the entries are written in.

The root is a member when its ledger has a `[package]` table. A root with none is a virtual root, as in uv: it holds the workspace and the shared lock and nothing to build.

Four things are refused, writing nothing: an entry that is not a path under the root, with an empty, `.`, `..` or `*` segment other than the `*` that ends it (so a leading `/`, `../x` and `a/*/b` are refused), a plain path that holds no committed ez.toml, a member whose ledger has its own `[workspace]` table (workspaces do not nest, in uv or in cargo), and two members with the same `[package] name`, since EZ-WS-5 finds a member by that name. "Committed" is the same reading `ez lock` already makes of the tree: what `git ls-files` lists, so an untracked member never reaches the lock (EZ-DOC-3).

**Update (W1):** the member set is `W.members` in `src/ws/workspace.bend`, a pure function of what `[workspace]` says, whether the root has a package, and the ledgers git lists under the root, each read as its directory, its `[package] name` and whether it has a `[workspace]` table. A path is read as its segments, so an entry, an exclusion and a member are compared segment by segment, and `<dir>/*` is a directory with exactly one segment more. The laws in `src/ws/LAWS.bend` state what an entry names, that a bad segment is refused wherever it stands, that the members are exactly the listed directories no exclusion takes back (`picks_exactly`), and that the set is had only when none of the four refusals applies. ez's own TOML view keeps string pairs and drops arrays, so `W.spec.of` reads `members` and `exclude` from eztoml's values directly, and an array holding anything but strings is refused rather than read as a shorter list. EZ-WS-1 stays pending until the reading of the ledgers is stated as a law and a command acts on the set, which W2 and W3 do.

## Finding the root (EZ-WS-2)

ez reads `ez.toml` from the directory it runs in. In a workspace that directory may be a member, so every command first finds its root: the nearest directory at or above it, up to the top of the git checkout, whose ledger is a workspace root that names the directory as a member. That is uv's search, cut off at the repository, since a member must be committed in the same repository as its root. A directory no root claims is a project of its own, exactly as today, so a project that is not a workspace sees no change.

The decision is a pure function of the directories above the one ez runs in and the ledger text found in each, which the interpreter reads, so a law quantifies over every arrangement of them.

What a command acts on follows uv:

| Command | Acts on |
| :-- | :-- |
| `ez lock`, `ez lock --upgrade` | every member's ledger; writes the root's lock |
| `ez fetch` | the root's lock |
| `ez doctor` | every member, and the root's lock |
| `ez add`, `ez remove` | the member's own ledger |
| `ez check`, `ez build`, `ez run` | the member's own entry, with the root's `BEND_LIB` |
| `ez publish` | the member's own package, judged against the root's lock (EZ-PUB-5) |

**Update (W2):** the search is `src/ws/root.bend`. `R.asks` names the directories whose ez.toml the interpreter reads, where ez runs first and the top of the checkout last, each with the path from it down to where ez runs, and `R.root.go` decides from what they hold in that order. A directory with no ez.toml, and one whose ledger has no `[workspace]` table, are passed by; the first workspace root that claims the directory is its root, a workspace root claiming itself and a directory below it exactly when EZ-WS-1 makes it a member; and a `[workspace]` table that cannot be read stops the search with its reason, since taking the directory for a project of its own would silently ignore the workspace above it. We read the path from `git rev-parse --show-prefix` (`R.here.of`), so the search stops at the top of the checkout without ez walking the filesystem. No command calls the search yet; each does as it is converted, from W3 on, so EZ-WS-2 stays pending until then.

## One lock (EZ-WS-3)

The lock is written at the root and nowhere else. A member's own `ez.lock.toml`, if one is left over from before it joined, is neither read nor written, and `ez doctor` says so. EZ-DOC-3 to EZ-DOC-5 are restated over the workspace's World, which holds every member's ledger text in place of one: the lock is a function of those ledgers and the committed tree, a rerun writes the same bytes, and a plain lock writes no ledger.

The lock already takes the hub imports of every committed `.bend` file under the root, so the files it reads do not change. What changes is that the ledger it resolves against is the union of the members' ledgers, checked by EZ-WS-4.

**Update (W3):** we did not give the lock planner a second kind of World. The lock planner's World holds a ledger's text, and every lock law (EZ-DOC-3 to EZ-DOC-5, EZ-OUT-1, EZ-OUT-2) quantifies over every World, so a workspace is locked by the same planner from one ledger that joins the members' (`src/ws/joint.bend`): the root's `[package]` table, then every dependency and tool of the root and of each member in the order git lists them, a member's relative path source anchored at the member's directory as EZ-LED-8 anchors one at the root, and each name at its first declaration (`firsts_find`). Members are joined only when every declaration of a name agrees with the first and every member names the root's hub, or none (`combine_needs_deps`, `combine_needs_tools`, `combine_needs_hub`). Two new lock laws say a plain lock writes no path but the lock's, so no member's ledger (`plain_lock_writes_only_lock`, `plain_lock_keeps_members`), and `lock_reproducible`, `lock_idempotent` and `plain_lock_keeps_ledger` carry EZ-WS-3 too, since a workspace's lock is one of the Worlds they are about. Base has no way to change directory, and every interpreter reads its paths from where it runs, so `ez lock`, `ez fetch` and `ez doctor` run in a member run again at the root with the same words (`src/ws/hop.bend`), and end as that run ends. On the binary, `ez lock` in `libs/a` of a workspace whose two members pin one path dependency wrote one lock at the root, recording the member's `../../../dep` as the root reads it, `../dep`; a rerun wrote the same bytes, two members pinning it at different revs were refused naming it, and ez's own lock was unchanged. `ez lock --upgrade` at a workspace root is refused until W4, since an upgrade writes back the ledger it planned from.

## One pin per source (EZ-WS-4)

In uv the whole workspace has one resolution, so two members cannot hold two versions of one package. ez pins exactly, so the same rule is that one git URL has one `rev` and one `tag` across the workspace. `ez lock` refuses a workspace whose members disagree, names both members and both pins, and writes nothing.

We keep the pin in each member's ledger rather than in a root table, so a member stays a complete ledger and `ez add` needs no new syntax. To make that workable, `ez add` in a member of a source another member already records takes that member's `rev` and `tag` when no ref is given, without asking the remote for refs, as `uv add` takes the version the workspace has already resolved. A ref that resolves to another commit is refused, naming `ez lock --upgrade --package <name>`, which moves the source in every member that records it, in one plan that writes every ledger it changes or none.

A hub dependency is pinned by its hash already, so two members with the same hub name at the same version agree by construction, and two versions of one hub name are two packages, as they are today.

**Update (W4):** the joint ledger is refused when a git source, as the root reads it, is declared at two commits or two tags (`combine_needs_pins`). `ez lock --upgrade` at a workspace root is planned on the joint ledger like a plain lock (`src/ws/up.bend`), so a source moves once for the whole workspace; the plan's one write of ez.toml, which would hold the joint ledger, is replaced by a write of every ledger the upgrade changed, the root's with its `[workspace]` table rendered back, each dependency and tool taking its new pin from the joint ledger and keeping its own source path and vendor bit (`pin_back`, `tool_pin_back`). Every other effect is kept, so the sources rewritten, `.gitignore` and the lock are the planner's (`up_writes_the_lock`), and a refusal still writes nothing (`up_refusal_writes_nothing`). For `ez add` we chose the plainest rule that keeps one pin: with no ref, a source the workspace pins is added at the tag it is pinned at, or its commit when it has none, which `ez add` resolves as any named ref; a ref that is neither is refused before anything is asked, rather than resolved and compared, since the answer is the same and refusing early asks the remote nothing (`src/ws/pin.bend`). A member's own commands run where they are, with BEND_LIB at the root's `.ez/lib` when the environment sets none, by running again in place with it set, and `ez publish` in a member reads the root's lock (`src/ws/hop.bend`, `lib_member`, `lock_member`). On the binary, `ez lock --upgrade` in `libs/b` moved `dep` in both members' ledgers, each keeping `../../../dep`, rewrote the import in `libs/a`, and left the root's ledger, which pins nothing, as it was; `ez add ../../../dep` in a new member took the workspace's `master` at its commit and laid the tree under the root's `.ez/lib`, and with the old commit as its ref it was refused and wrote nothing.

## Member dependencies (EZ-WS-5 to EZ-WS-7)

A member depends on another with a section that names it by its `[package] name`:

```toml
[deps.parse]
workspace = true
```

This is uv's `{ workspace = true }` source. The section records no `hash` and no `git`, because the member's hash is a fact about the committed tree, worked out from the member's own entry by the package walk (`src/pkg/pkg.bend`), the same walk `ez add` and `ez publish` run. Recording it in a ledger would make the ledger stale on every edit, and a plain `ez lock` may not write one (EZ-DOC-5). `ez lock` records each member's hash in the lock and lays its walked tree under `BEND_LIB/<hash>`, where bend looks for it. A `workspace = true` section that names no member, or names its own member, is refused.

How a member is imported depends on whether it has a published name, as it does today for a package from outside.

### Named members (EZ-WS-6)

A member whose ledger gives `publish-as` and `version` is imported by that name: `import parse@1.2.0.0/lib.bend as Parse`. `ez lock` resolves the name to the member's hash, records the pair under `[names]`, and lays `BEND_LIB/names/parse@1.2.0.0`. A member is never asked about on the hub, and the lock being rewritten is never read for it, since the committed tree is the answer.

This is the editable install of the design: editing `parse` and running `ez lock` moves the hash under the name and rewrites no source. It is also what the import says once `parse` is published under that name, so a member's files are the same whether its dependency comes from the workspace or from the hub.

EZ-HUB-1 says a name resolves to the one ez.toml records for it, else the lock's, else the hub's. In a workspace a member's name has to come first, so EZ-HUB-1 becomes "the one a member of the workspace is published as, else the one ez.toml records for that name, else the one the lock being rewritten records, else the one the hub answers", and EZ-HUB-2 gains "nor a member is published as it". Both rows read as before for a project that is not a workspace.

### Members by hash (EZ-WS-7)

A member with no published name is imported by its `0x` hash, as a git dependency with no hub name is today. Its hash moves when it is edited, and the import lines naming it do not. We treat that the way a moved git dependency is treated now: a plain `ez lock` reads, in the lock being rewritten, the hash it last recorded for each member, and when an import line names a member's old hash it refuses, names the member and `ez lock --upgrade --package <name>`, and writes nothing.

The upgrade rewrites those lines exactly as EZ-VEN-2 and EZ-VEN-3 rewrite a moved dependency's. A rewritten file can belong to another member imported by hash, whose hash then moves too, so the upgrade carries on to it, until no import line names a moved member's old hash. Hash imports cannot form a cycle, since a package's hash covers what it imports, so this ends, and the moves are applied in the order they were found, which satisfies `moves.ok`'s premise that no move's new hash is a later move's old one.

On a fresh clone, every import already names the hash the committed tree walks to, so nothing moves and the lock reproduces (EZ-DOC-3).

## Fetch and doctor (EZ-WS-8, EZ-WS-9)

`ez fetch` lays a member's package from the committed tree, never from the hub or a clone, and only when its walk hashes to what the lock records for it. A member edited since the lock was written is refused by name, so `ez fetch` never lays a tree the lock does not describe (EZ-FETCH-1).

`ez doctor` runs its drift check per member, each member's import lines against its own ledger, because a dependency is declared where it is used. It judges the root lock as EZ-VEN-6 does, over every member's ledger, and reports a member whose committed tree no longer walks to the hash the lock records.

## Work packages

| WP | Lands | Rows |
| :-- | :-- | :-- |
| W1 (landed) | `[workspace]` read beside the ledger model, in `src/ws/workspace.bend`; the member set as a pure function of the root ledger and the committed listing | EZ-WS-1 |
| W2 (landed) | Root finding as a pure function of the directories above and their ledgers; every command's interpreter reads the ancestors and calls it | EZ-WS-2 |
| W3 (landed) | The lock planned from the members' joint ledger; one lock at the root; EZ-DOC-3 to EZ-DOC-5 hold of it as of any World | EZ-WS-3 |
| W4 (landed) | The one-pin check in the lock; `ez add` reusing a member's pin; `ez lock --upgrade` moving a source in every member | EZ-WS-4 |
| W5 | `workspace = true` sources (a `Member` constructor of `M.Source`); the lock walks each member and lays it | EZ-WS-5 |
| W6 | Named members resolved before the ledger, the lock and the hub; EZ-HUB-1 and EZ-HUB-2 reworded | EZ-WS-6 |
| W7 | Moved hash members refused by a plain lock and rewritten by the upgrade | EZ-WS-7 |
| W8 | `ez fetch` and `ez doctor` over a workspace | EZ-WS-8, EZ-WS-9 |

W1 and W2 come first, since every later package needs the member set and the root. W5 adds a constructor to `M.Source`, which every match on a source has to handle, so it lands before W6 and W7 and after W4, whose check is over git sources only.

## Known gaps

`ez init` in a directory under a workspace root makes a project of its own and does not add it to `members`, where `uv init` adds it. `members` takes no glob but `<dir>/*`. A workspace member cannot be a `[tools.*]` pin of another member.
