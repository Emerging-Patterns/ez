# ez.toml and ez.lock.toml

This page defines the two files ez keeps in a project: what each key means,
and what a tool that rewrites them must keep. It describes lock version 2.
The [guide](guide.md) says which command writes what; [SPEC.md](../SPEC.md)
holds the requirements cited here.

## The two files

| File | Written by | Holds |
| :--- | :--- | :--- |
| `ez.toml`, the ledger | a person, `ez init`, `ez add`, `ez remove`, `ez lock --upgrade` | the package, its direct dependencies and tools, each pinned to one source and hash |
| `ez.lock.toml`, the lock | `ez lock`, and the commands that lock after editing the ledger | every package of the closure with its source and files, the names it resolved, the tools |

Reading the ledger never picks a version. Plain `ez lock` never writes
ez.toml and records every pin exactly as ez.toml has it (EZ-DOC-5).

## Hashes

- **File digest.** The lowercase hex SHA-256 of a file's bytes, 64
  characters. This is the digest `bend --publish` and the hub name a file by.
  A lock an older ez wrote may hold a digest of each character's low eight
  bits instead; on ASCII files the two are the same, and a reader may accept
  either.
- **Package hash** (`0x` hash). `0x` followed by the first 32 hex characters
  of the SHA-256 of the package's manifest text. The manifest is one line per
  file of the package, `<digest> <path>\n`, sorted by path. The package's
  files are the import closure of its entry, plus every file named exactly
  `LICENSE` beside one of them, as `bend --publish` takes them. A package hash matches `0x[0-9a-f]{32}`.
- **narHash.** The SRI SHA-256 of a git checkout in NAR serialization, with
  the top-level `.git` removed and without submodules, as `nix hash path
  --sri` reports it (`sha256-…`).
- **Name.** A hub `<name>@<version>`, matching
  `[a-z][a-z0-9-]{0,63}@N.N.N.N` where each `N` is a decimal with no leading
  zero. A name the hub has answered names the same hash forever (EZ-TRUST-6).

## The TOML ez reads and writes

Both files are a subset of TOML that eztoml reads and writes:

- Every value is a basic string with no `"`, no `\` and no newline, except
  the booleans `vendor` and `workspace`, written bare, and `[workspace]`
  `members` and `exclude`, which are arrays of such strings. ez refuses to
  write a value that breaks this, and writes nothing (EZ-LED-4).
- A key with an empty value is not written. An absent key and an empty one
  mean the same thing.
- Paths use `/` on every system.
- ez writes the parent tables (`[deps]`, `[tools]`, `[packages]`) as empty
  headers. A reader must not depend on them.

ez rewrites ez.toml from its model of the file, so a key this page does not
define is dropped the next time ez writes the ledger. Comments are dropped
too.

## ez.toml

```toml
[package]
name = "myapp"
entry = "src/main.bend"

[deps.sha256]
hash = "0x3bdc0c9f5265bb49f7fc76b61f529f24"
git = "https://github.com/noah-emp/bend-sha256"
rev = "f6c04a400b83cb927ea76b939d9351ef426e370d"
root = "."
narHash = "sha256-Tu8uurWltf6TQd0mNO10BTQq5WYPKrLhOAa+GZRp/zY="
entry = "package.bend"

[deps.json]
hash = "0x…"
hub = "emerging-ezjson@1.2.0.0"

[tools.bolt]
git = "https://github.com/Emerging-Patterns/bolt"
rev = "358c2da98df8d2d15c5ceaa3a56521212b9029ca"
tag = "v1.17.0"
root = "."
narHash = "sha256-J+XYAGvL7FOs4NgRwGG8itNlYTIQBM7dNq/r5nrB1Z8="
entry = "main.bend"
```

### `[package]`

| Key | Meaning |
| :--- | :--- |
| `name` | the package's name |
| `entry` | the file the package's imports start from; `main.bend` when absent |
| `bin` | the file `ez build`, `ez run` and the tool commands build; the entry when absent |
| `hub` | the hub the packages come from; `https://hub.bend-lang.com` when absent |
| `publish-as` | the hub name `ez publish` names the package by; absent publishes it by hash alone |
| `version` | the version `ez publish` names it with |

A root ledger with no `[package]` table is a virtual workspace root.

### `[workspace]`

| Key | Meaning |
| :--- | :--- |
| `members` | directories relative to the root, each a path or `<dir>/*` for every directory directly under `<dir>` |
| `exclude` | directories taken back out |

A member's own ez.toml must not have a `[workspace]` table. See the
[workspaces design](rfc/ez-workspaces.md).

### `[deps.<name>]`

`<name>` is the dependency's name in this project, a TOML bare key. Import
lines never use it: they use the hash, or the `hub` name. The sections list
the packages this project imports directly. The rest of the closure is the
lock's job.

Every section has:

| Key | Meaning |
| :--- | :--- |
| `hash` | the package's `0x` hash. Required, except for a workspace member |
| `entry` | the file inside the package the hash was computed from |

The other keys say where the bytes come from. There are three kinds of
source.

**Hub.** No `git` key and no `workspace` key.

| Key | Meaning |
| :--- | :--- |
| `hub` | the `<name>@<version>` the dependency was added by, when it was added by name. It is the name the project's import lines use. Not a bare name. |

**Git.** A `git` key. For a package the hub never published, or one pinned
to a commit.

| Key | Meaning |
| :--- | :--- |
| `git` | the repository URL, or a local path as it was given |
| `rev` | the full commit |
| `tag` | the tag that was asked for, which `ez lock --upgrade` re-resolves; absent for a commit pin |
| `root` | the directory inside the checkout the package's paths are written from; `.` when absent |
| `narHash` | the checkout's narHash, which nix fetches it by |
| `vendor` | `true` when the package is committed under `.ez/lib` (EZ-VEN-1) |

**Workspace member.** `workspace = true`, and no `hash` and no other source
key. The section's name is the member's `[package] name`, and its package
is the member's committed tree.

### `[tools.<name>]`

A pinned CLI. It is not a package: it has no `hash`, is not imported and is
not put on `BEND_LIB` (EZ-LED-5). It takes the git keys above, plus:

| Key | Meaning |
| :--- | :--- |
| `entry` | the file to build, when the tool's own ledger should not decide |
| `bin` | the binary file to build, likewise |

A tool pin may name only `git`; `ez lock --upgrade` fills its `rev`, `tag`
and `narHash`.

## ez.lock.toml

```toml
[lock]
version = "2"
hub = "https://hub.bend-lang.com"

[packages."0x3bdc0c9f5265bb49f7fc76b61f529f24".source]
kind = "git"
url = "https://github.com/noah-emp/bend-sha256"
rev = "f6c04a400b83cb927ea76b939d9351ef426e370d"
entry = "package.bend"
root = "."
narHash = "sha256-Tu8uurWltf6TQd0mNO10BTQq5WYPKrLhOAa+GZRp/zY="

[packages."0x3bdc0c9f5265bb49f7fc76b61f529f24".files]
"core.bend" = "bece2919b7a164b125bce89c0b893448067971ef3f754febd519c47408b94706"
"package.bend" = "e9b20f06fd38bda4647198d28e1c18cbbe092bb60b79db134bb705efb6fc9da7"

[names]
"emerging-ezjson@1.2.0.0" = "0x…"

[tools.bolt]
git = "https://github.com/Emerging-Patterns/bolt"
rev = "358c2da98df8d2d15c5ceaa3a56521212b9029ca"
tag = "v1.17.0"
root = "."
narHash = "sha256-J+XYAGvL7FOs4NgRwGG8itNlYTIQBM7dNq/r5nrB1Z8="
entry = "main.bend"
```

The tables come in this order: `[lock]`, the packages in hash order, `[names]`,
then the tools in ledger order. Each package's files are in path order. The
text depends only on what was resolved, not on the order it was found in
(EZ-DOC-2), and a fresh clone locks to the same bytes (EZ-DOC-3).

### `[lock]`

| Key | Meaning |
| :--- | :--- |
| `version` | `"2"` |
| `hub` | the hub the packages were resolved against, and the base URL of a hub file: `<hub>/<hash>/<path>` |

A lock an older ez wrote may hold a bend version here. Nothing reads it.

### `[packages."<hash>".source]`

One per package of the closure, direct or not, keyed by its `0x` hash.

| `kind` | Other keys |
| :--- | :--- |
| `hub` | none |
| `git` | `url`, `rev`, `entry`, `root`, `narHash`, and `tag` when one was asked for |
| `member` | `path`, the member's directory from the workspace root, and `entry` |

The git keys mean what they mean in ez.toml; `url` is the ledger's `git`.

### `[packages."<hash>".files]`

Every file of the package, as `"<path>" = "<digest>"`, the
path relative to the package's root. A reader rebuilds the manifest from this
table and checks it against the hash.

### `[names]`

Every `<name>@<version>` the lock resolved, with the `0x` hash it names, in
name order. Absent when nothing was imported by name. `ez fetch` lays each
one as `BEND_LIB/names/<name>@<version>`, holding the hash and a newline
(EZ-HUB-4).

### `[tools.<name>]`

The ledger's `[tools.<name>]` pin, with the same keys, filled in.

## Rewriting these files

A tool that writes ez.toml keeps:

- **Every source key of every section.** A git dependency is fetched by
  `git` and `rev`, laid out from `root`, and fetched by nix by `narHash`.
- **`tag`.** `ez lock --upgrade` re-resolves it. A dependency with no `tag`
  is a commit pin.
- **`vendor`.** The `.gitignore` allowlist is made from it.
- **`hub` as `<name>@<version>`.**
- **`[deps]` as direct dependencies only.**
- **`[tools.*]` and `[workspace]`.**

ez.lock.toml is ez's output. Another tool may read it. A tool that writes it
must write text `ez lock` would write from the same ledger, or `ez lock` will
rewrite it.
