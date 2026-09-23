# ez specification

This is the list of every behavior ez guarantees, each under a stable requirement ID. Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law in a LAWS.bend that passes the proof gate. A **Trusted** requirement is an assumption about something ez cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose law has not landed yet has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: for every PROOF.bend in the tree, the first line `bend PROOF.bend` prints is exactly `All terms check.` `ez prove` runs it, and it is the check CI runs.

The reasoning behind each requirement, and the decisions that shaped them, are in [docs/rfc/ez-spec.md](docs/rfc/ez-spec.md).

## Tagging

A quantified law that proves a requirement carries the requirement's ID in a comment directly above its `law` line:

```
# EZ-HASH-1
law hash_perm:
```

A closed law that illustrates a pending requirement is marked `# toward EZ-X-N` directly above its `law` line. It is a trail, not a proof, and we delete it in the same change that lands its requirement's quantified law. bolt's `quantify` rule (L004), on at `error` in `bolt.bend`, rejects any other law without a binder.

A pending requirement may already have tagged quantified laws that prove part of it. The Law column names them, and "Left to prove" below says what is missing before the status becomes proved.

Untagged quantified laws are allowed. They pass the proof gate like any law, but nothing here protects them, so a change may edit or delete them freely.

## Requirements

### Hashing (EZ-HASH)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-HASH-1 | The 0x hash of a file list with distinct paths depends only on its (path, sum) pairs, not on the order they were found in. | Proved | proved | pkg/LAWS.bend hash_perm |
| EZ-HASH-2 | The NAR serialization of a directory does not depend on the order its entries are listed in. | Proved | pending | |
| EZ-HASH-3 | When ez writes a package under `<lib>/<h>`, `h` is the 0x hash of the file list whose manifest it writes beside the files. | Proved | pending | |
| EZ-HASH-4 | ez's 0x hash for an entry equals the hash `bend --publish` assigns to it. | Trusted | | |
| EZ-HASH-5 | ez's narHash equals `nix hash path --type sha256 --sri` of the same tree. | Trusted | | |
| EZ-HASH-6 | `Sha.hex(s)` is the SHA-256 of the UTF-8 bytes of `s`. For a file's text that is SHA-256 of the file's bytes, which is what `bend --publish` and the hub compute. | Trusted | | |

### Ledger (EZ-LED)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-LED-1 | A ledger that does not parse is never read into a model, and renders as nothing, so no command writes a guess over it. | Proved | pending | |
| EZ-LED-2 | Adding a dependency to a ledger model twice is adding it once. | Proved | pending | |
| EZ-LED-3 | Removing a dependency from a ledger model twice is removing it once. | Proved | pending | |
| EZ-LED-4 | A ledger ez rendered parses back to the model it was rendered from. | Proved | pending | |
| EZ-LED-5 | A `[tools.*]` section is a tool, never a dependency, and needs no `hash`. | Proved | pending | |

### Lock document (EZ-DOC)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-DOC-1 | Parsing a rendered lock yields the packages, hub and tools that were rendered. | Proved | pending | |
| EZ-DOC-2 | Packages are written in hash order and each package's files in path order, so the lock's text does not depend on the order the walk found them in. | Proved | pending | |
| EZ-DOC-3 | `ez lock` output is a function of the ledger and the committed tree. A fresh clone reproduces the lock byte for byte. | Proved | pending | |
| EZ-DOC-4 | `ez lock` is idempotent: run on the world it just produced, it writes the same bytes. | Proved | pending | |
| EZ-DOC-5 | `ez lock` without `--upgrade` never changes a dependency's pinned rev, and changes a tool's only when the ledger left it empty. | Proved | pending | |

### Resolution (EZ-RES)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-RES-1 | `ez add` with no ref pins the greatest semver-ish release tag on the remote; with no release, the greatest pre-release; with no semver-ish tag, the remote's default branch as its `HEAD` symref names it. A named ref resolves exactly, as `refs/tags/<ref>` and then `refs/heads/<ref>`. A 40-hex ref is used as a commit without asking the remote. | Proved | pending | |
| EZ-RES-2 | `ez add` with no entry uses the revision's `[package] entry`, then `[package] bin`, then `main.bend`, and refuses if that file is not in the revision. | Proved | pending | |
| EZ-RES-3 | A target containing `://` or starting `git@` is a git URL. A target starting `/`, `./`, `../` or `~/` is a path. A target of exactly two segments of letters, digits, `-`, `_` and `.`, neither of them `.` or `..`, is `https://github.com/<target>`, unless its second segment ends in `.bend`, which makes it a path. Anything else is a path, except the empty word, which is refused. | Proved | proved | ez/LAWS.bend classify_url, classify_scp, classify_abs, classify_here, classify_up, classify_home, classify_github, classify_else |
| EZ-RES-4 | `ez lock --upgrade` never moves a hub dependency. | Proved | pending | |
| EZ-RES-5 | An upgraded rev-only dependency moves to the default branch tip only when its pin is an ancestor of that tip, and stays a commit pin. Otherwise the upgrade refuses with exit 1. | Proved | pending | |
| EZ-RES-6 | `--package NAME` asks the remote only for the named dependency or tool, and every other ledger entry keeps its rev, tag and hash. | Proved | pending | |
| EZ-RES-7 | Tags, refs, and ancestry reported by git are accurate. | Trusted | | |
| EZ-RES-8 | An upgraded tagged dependency re-resolves its tag. A tag that now names a commit the pin does not descend to, or a pinned commit whose tree no longer hashes to the pin, stops the upgrade with exit 1. | Proved | pending | |

### Vendoring and source rewriting (EZ-VEN)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-VEN-1 | After `ez add`, `ez remove` or `ez lock --upgrade`, the `.gitignore` allowlist names exactly the hashes of dependencies marked `vendor = true`, and every other line of `.gitignore` is unchanged. | Proved | pending | manifest/LAWS.bend allowlist_is_the_ledger, allowlist_keeps_other_lines |
| EZ-VEN-2 | When an upgrade moves a hash, every line of a `.bend` file outside `.ez` and `.git` that starts `import <old>/` names `<new>` afterwards. | Proved | pending | |
| EZ-VEN-3 | Import rewriting leaves every other line of every file byte-identical, and does not write a file with no matching line. | Proved | pending | |
| EZ-VEN-4 | `ez doctor` never writes to the project's source files. | Proved | pending | |
| EZ-VEN-5 | `ez doctor` reports every hash an import line names that the ledger does not, and every ledger dependency no import line names, and exits 1 when it reports any. | Proved | pending | |

### Fetch (EZ-FETCH)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-FETCH-1 | `ez fetch` writes a package file under `BEND_LIB` only when its digest matches the lock: a hub body's digest starts with the lock's sum, a git file's digest equals it. | Proved | pending | |

### Tools (EZ-TOOL)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-TOOL-1 | The link directory is `$EZ_TOOL_BIN`, else `$XDG_BIN_HOME`, else `$HOME/.local/bin`, an empty value counting as unset. | Proved | pending | |
| EZ-TOOL-2 | A cached binary is reused only when the recorded commit, built file and bend version all equal the resolved ones, and never when the resolved commit is empty. A cached checkout is reused only when its recorded commit equals the resolved one. | Proved | proved | ez/LAWS.bend key_rev_differs, key_file_differs, key_bend_differs, key_no_rev, key_same_reuses, checkout_differs, checkout_same |
| EZ-TOOL-3 | A local target with uncommitted or untracked changes, or a path that is not a checkout, resolves to no commit and is rebuilt on every run. | Proved | pending | |
| EZ-TOOL-4 | A target naming a `[tools.*]` pin in ez.toml builds the lock's rev, url, entry and bin. An `owner/repo` or URL target builds `git ls-remote <url> HEAD`. A path builds its clean `HEAD`. | Proved | pending | |
| EZ-TOOL-5 | `ez tool run` exits with the built program's status; any failure before the program runs exits 1. | Proved | pending | |
| EZ-TOOL-6 | `ez tool install` and `ez tool upgrade` never run the built binary. | Proved | pending | |
| EZ-TOOL-7 | The built file is the pin's `bin`, then the pin's `entry`, then the checkout's `bin`, then its `entry`, then `main.bend`. The link is named after the checkout's package name, or `app`. | Proved | pending | |
| EZ-TOOL-8 | A remote target whose cache slug is empty, absolute, or climbs with `..` is refused. | Proved | pending | |
| EZ-TOOL-9 | `ez tool run <target>` passes every word after the target to the program, dropping one leading `--`. `ez run` passes every word after `run` to the entry. | Proved | pending | |

### Publish (EZ-PUB)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-PUB-1 | `ez publish` refuses when `git status --porcelain --untracked-files=normal` names any path. | Proved | pending | |
| EZ-PUB-2 | `ez publish` succeeds only when a line of bend's output is exactly a `0x` name and equals ez's own hash. Any other answer exits 1. | Proved | pending | |

### Exit status (EZ-OUT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| EZ-OUT-1 | Every command exits 0 on success and 1 on any failure ez detects, except `ez tool run`, which exits with the program's status. | Proved | pending | |

## Left to prove

What stands between a pending requirement that has tagged laws and the status proved.

| ID | Proved so far | Left to prove |
| :---- | :---- | :---- |
| EZ-VEN-1 | Over the line-level function `I.lines` (manifest/ignore.bend): its allowlist lines are exactly the vendored hashes, in ledger order, and every other line is kept in order. | The text layer: `I.sync` splitting `.gitignore` into lines and joining them back, including the trailing newline, so that "every other line is unchanged" holds of the file's bytes. That applying it twice is applying it once. The commands calling it are interpreter code and stay trusted (EZ-TRUST-2). |

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| EZ-TRUST-1 | The Bend checker is sound. | We cannot check it from inside Bend. The BendTT paper and a Lean formalization exist, and the release notes report mismatches between the formalization and the implementation. |
| EZ-TRUST-2 | The interpreter reads the World and executes plans faithfully. | It makes no decisions and is kept small enough to review line by line. |
| EZ-TRUST-3 | The hub serves, for a hash, what was published under it. | ez checks every hub body against the hash it asked for (EZ-FETCH-1), so this reduces to availability and EZ-HASH-6. |
| EZ-TRUST-4 | `ez prove` runs `bend` on every PROOF.bend in the tree and passes only on an exact `All terms check.` first line. | It is ez code run by `mkProofs`, not a law. CI builds from a clean tree, so nothing is cached. |
| EZ-TRUST-5 | HTTP framing and URL parsing are correct. | Proved in ezhttp v0.4.0, the rev ez.toml pins; ez's gate does not re-check it. |
| EZ-RES-7 | git reports refs, tags, and ancestry accurately. | The World model takes git's answers as given. |
| EZ-HASH-4 | ez's 0x hash matches `bend --publish`. | The publisher is a separate program. |
| EZ-HASH-5 | ez's narHash matches nix. | nix is a separate program. |
| EZ-HASH-6 | `Sha.raw` computes the SHA-256 digest of its bytes, and `Sha.hex` of its text's UTF-8. | Proved in Giulio2002/bend-sha256 against an executable FIPS 180-4 specification, at the hash ez vendors; ez's gate does not re-check it. Collision resistance is also assumed. |
