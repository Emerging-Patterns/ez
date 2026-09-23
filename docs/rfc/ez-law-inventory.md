# ez law inventory

This is the companion to [ez-spec.md](ez-spec.md). It records what ez's LAWS.bend files actually state today, read from the source at `f009e42` ("Compute narHash without nix"), and maps each law to the requirement in the RFC it points toward.

## How to read the table

**Kind** is `Q` for a quantified law (it has at least one `for` binder) and `C` for a closed law (no binders, one fixed input).

**Proof** is `refl` when the whole proof in PROOF.bend is `{==}`, meaning the two sides reduce to the same term without any case split or induction. For a closed law that is expected. For a quantified law it means the binders are never inspected: the claim holds by unfolding definitions, and the law says little beyond what the definition already says. `struct` means the proof does real work (matching, recursion, rewrites).

**Points toward** names the RFC requirement the law supports. `none` means no current RFC requirement covers it. Where the law covers behavior the RFC should probably add, the entry says `new:` and a short name for that behavior; those are collected in the step 7 findings. `refactor-eq` marks a law that holds a rewritten definition equal to the slower one it replaced, which is a refactoring guarantee rather than a behavioral one.

We could not re-run `bend PROOF.bend` while writing this: the sandbox has no `bend`. Every law listed is present in LAWS.bend with a matching `def Laws.<name>` in PROOF.bend, and no PROOF.bend file mentions `unsafe`, `trust`, `admit`, or similar.

## Summary

| File | Laws | Quantified | Closed | Quantified by `refl` |
| :---- | ----: | ----: | ----: | ----: |
| ez/LAWS.bend | 94 | 11 | 83 | 1 |
| git/LAWS.bend | 13 | 11 | 2 | 1 |
| hub/LAWS.bend | 5 | 3 | 2 | 3 |
| io/LAWS.bend | 4 | 2 | 2 | 2 |
| lock/LAWS.bend | 11 | 7 | 4 | 2 |
| manifest/LAWS.bend | 53 | 32 | 21 | 6 |
| net/LAWS.bend | 30 | 29 | 1 | 2 |
| pkg/LAWS.bend | 40 | 38 | 2 | 9 |
| pub/LAWS.bend | 14 | 14 | 0 | 5 |
| sha/LAWS.bend | 5 | 0 | 5 | 0 |
| **Total** | **269** | **147** | **122** | **31** |

What ez proves today, in one paragraph: the 0x hash of a package's file set is independent of the order the files were found in (`pkg/hash_perm`, for file lists with distinct paths), which is EZ-HASH-1 already Proved. The lock cache cannot override the ledger for a given hash (`lock/origin_agrees`), which is a real fragment of EZ-DOC-3. The ledger parser and renderer have a strong quantified structure (add and remove are idempotent, sections are read in order, a bad read never renders). The HTTP client's framing, the `ez publish` hash check, and the path algebra are proved for all inputs. Everything about upgrade decisions, lock rendering order, lock round-tripping, import rewriting, the gitignore allowlist, target classification, NAR hashing, and SHA-256 is closed: pinned on one example each.

**Update:** no closed law remains. The first rollout phase deleted the 78 that pointed toward no Proved requirement and kept the rest as `# toward` trails. The last 40 trails were deleted together, with their proofs and the sample values only they used, when ez moved to the bolt with a strict `closed` rule and the `trace` rule. They were, by requirement:

- EZ-DOC-1: `lock/LAWS.bend` `lock_roundtrip`, `tool_pin_reads_back`.
- EZ-DOC-2: `lock/LAWS.bend` `hashes_sorted`.
- EZ-DOC-4: `manifest/LAWS.bend` `same_rev_keeps`.
- EZ-LED-4: `manifest/LAWS.bend` `render_parse_roundtrip`, `bolt_rev`.
- EZ-LED-5: `manifest/LAWS.bend` `tool_needs_no_hash`, `tool_is_not_a_dep`, `bolt_is_a_tool`, `bolt_is_not_a_dep`; `lock/LAWS.bend` `tools_are_not_packages`.
- EZ-RES-4: `manifest/LAWS.bend` `hub_holds`.
- EZ-RES-5: `manifest/LAWS.bend` `sha256_aims_forward`, `sha256_advances`, `sha256_retarget`; `git/LAWS.bend` `sha256_remote_tip`, `sha256_remote_branch`.
- EZ-RES-6: `manifest/LAWS.bend` `unselected_holds`.
- EZ-RES-8: `manifest/LAWS.bend` `tag_follows`, `same_rev_drifts`, `tag_moved_off`.
- EZ-VEN-2: `manifest/LAWS.bend` `imports_follow_hash`.
- EZ-VEN-5: `ez/LAWS.bend` `hash_of_import`, `hash_of_relative`, `imported_dedups`, `report_agrees`, `report_both_ways`, `report_unused`.
- EZ-TOOL-7: `ez/LAWS.bend` `file_bin`, `file_entry`, `file_default`, `out_name_empty`, `out_name`.
- EZ-TOOL-8: `ez/LAWS.bend` `target_escapes`.
- EZ-TOOL-9: `ez/LAWS.bend` `argv_of_run`, `argv_of_tool`, `tool_rest_dashes`, `tool_rest_plain`.
- EZ-FETCH-1: `hub/LAWS.bend` `hash_match`, `hash_refuse`.

The tables below keep the closed laws as they were at `f009e42`; none of them is in the tree now.

## Inventory

### sha/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| hex_empty | C | refl | `Sha.hex("")` is the FIPS empty digest. | EZ-HASH-6 |
| hex_abc | C | refl | `Sha.hex("abc")` is the FIPS `abc` vector. | EZ-HASH-6 |
| hex_manifest | C | refl | One fixed manifest line hashes to a fixed digest. | EZ-HASH-6 |
| sri_empty_digest | C | refl | `Nar.sri.hex` of the empty digest is its base64 SRI. | EZ-HASH-5 |
| sri_empty_dir | C | refl | The NAR SRI of an empty directory matches what `nix hash path --sri` prints. | EZ-HASH-5 |

**Update:** WP8 of [ez-lock-planner.md](ez-lock-planner.md) adds `nar_dir_order_free`, tagged `# EZ-HASH-2`:

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| nar_dir_order_free | Q | struct | `Nar.dir` of a Lehmer-permuted entry list with distinct names is `Nar.dir` of the list. An entry is a `K.File` holding a name and its node's serial, and the proof is `pkg/sort_perm` carried under `Nar.directory`. | EZ-HASH-2 (this is the law) |

### hub/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| judge_have | Q | refl | A fetched body whose digest starts with the asked-for hash is `Have{body}`. | EZ-TRUST-3 (new: hub bodies are verified) |
| judge_refuse | Q | refl | A body whose digest does not match is `Miss` with a fixed reason. | EZ-TRUST-3 (new: hub bodies are verified) |
| judge_miss | Q | refl | A `file://` that did not arrive is `Miss`, not an empty `Have`. | EZ-TRUST-3 (new: hub bodies are verified) |
| hash_match | C | refl | One fixed manifest matches its 32-char prefix. | EZ-TRUST-3 |
| hash_refuse | C | refl | One fixed manifest does not match an unrelated prefix. | EZ-TRUST-3 |

### io/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| write_ok | C | refl | `F.write.ok(Done{Unit})` is `True`. | none (interpreter) |
| write_read | Q | refl | `F.text_of(Some{s}) == s`. The comment claims a written file reads back; the law only unwraps a `Some`. | none (interpreter) |
| read_miss | Q | refl | A failed open reads as `None`, not `""`. | none (interpreter) |
| text_of_none | C | refl | `F.text_of(None) == ""`, so a missing file reads as empty text downstream. | none (interpreter) |

### pkg/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| dedup_dup | Q | struct | `dedup` collapses an adjacent repeated file. | EZ-HASH-1 |
| dedup_keeps | Q | struct | `dedup` of a non-empty list is non-empty. | EZ-HASH-1 |
| base_last | Q | struct | `Path.base.last` of a list ending in `x` is `x`. | none (path lemma) |
| sort_perm | Q | struct | `file.sort` is invariant under any Lehmer-coded permutation of a distinct-path file list. | EZ-HASH-1 |
| manifest_perm | Q | struct | `manifest_of` is invariant under permutation (distinct paths). | EZ-HASH-1 |
| hash_perm | Q | struct | `hash_of`, the 0x name, is invariant under permutation (distinct paths). | EZ-HASH-1 (this is the law) |
| join_agrees | Q | struct | New `Path.join` equals the old double-normalising join. | refactor-eq |
| stmt_of_agrees | Q | struct | New line classifier equals the old one. | refactor-eq |
| escaped_agrees | Q | struct | New escaping-path search equals the old one. | refactor-eq |
| seen_has_agrees | Q | struct | New seen-set scan equals the old one. | refactor-eq |
| comp_name | Q | struct | A component other than `""`, `.`, `..` is kept verbatim. | EZ-HASH-4 (supporting) |
| up_cancels | Q | struct | `..` cancels a preceding non-`..` component. | EZ-HASH-4 (supporting) |
| up_stacks | Q | refl | `..` after `..` stacks. | EZ-HASH-4 (supporting) |
| split_plain | Q | struct | A slashless string splits into itself. | none (path lemma) |
| base_plain | Q | struct | `base` of a slashless path is the path. | none (path lemma) |
| tail_plain | Q | struct | `tail(p, 1+q)` of a slashless path is the path. | none (path lemma) |
| dir_is_climb | Q | struct | `dir(p) == join(p, "..")` for non-empty `p`. | none (path lemma) |
| ups_climb | Q | refl | A leading `../` adds one to `ups`. | EZ-HASH-4 (supporting) |
| unbend_plain | Q | struct | A path not ending `.bend` is unchanged by `unbend`. | EZ-HASH-4 (supporting) |
| walk_keeps_root | Q | struct | Normalisation preserves the absolute flag. | none (path lemma) |
| norm_absolute | Q | struct | `norm` of an absolute path is absolute. | none (path lemma) |
| climb_absolute | Q | struct | `climb(n, p)` of an absolute path is absolute. | none (path lemma) |
| comp_dot | C | refl | `.` is a skipped component. | none (path lemma) |
| skip_id | Q | struct | A skipped component leaves the walk unchanged. | none (path lemma) |
| norm_dot | Q | struct | `norm("./" ++ p) == norm(p)` for relative `p`. | EZ-HASH-4 (supporting) |
| empty_is_here | C | refl | `norm("") == "."`. | none (path lemma) |
| dir_plain | Q | struct | `dir` of a single real component is `.`. | none (path lemma) |
| join_bare | Q | refl | `join("", p) == norm(p)`. | none (path lemma) |
| climb_zero | Q | refl | `climb(0, p) == norm(p)`. | none (path lemma) |
| unbend_ext | Q | struct | `unbend(p ++ ".bend") == p`. | EZ-HASH-4 (supporting) |
| ups_plain | Q | struct | A slashless non-`..` path has zero climbs. | none (path lemma) |
| tail_one | Q | struct | `tail(p, 1) == base(p)`. | none (path lemma) |
| hub_needs_0x | Q | struct | A spec not starting `0x` is not a hub import. | EZ-HASH-4 (supporting) |
| hub_needs_slash | Q | struct | A spec with no `/` is not a hub import. | EZ-HASH-4 (supporting) |
| hub_named | Q | struct | `0x<h>/<rest>` is a hub import. | EZ-HASH-4 (supporting) |
| late_mod | Q | refl | An import after the header ends is dropped. | EZ-HASH-4 (supporting) |
| header_mod | Q | refl | An import inside the header is kept. | EZ-HASH-4 (supporting) |
| body_ends | Q | refl | A body line closes the header. | EZ-HASH-4 (supporting) |
| foreign_keeps_head | Q | refl | A foreign body is collected wherever it appears. | EZ-HASH-4 (supporting) |
| hash_is_prefix | Q | refl | `hash_of(xs) == "0x" ++ take(sha(manifest_of(xs)), 32)`. | EZ-HASH-1, EZ-HASH-4 (definition of the 0x name) |

### lock/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| origin_first | Q | struct | The first origin recorded for a hash wins over later ones. | EZ-DOC-3 |
| origin_agrees | Q | struct | For a hash the ledger records, the origin is the same whatever `.ez/origins.toml` holds. The ledger wins outright. | EZ-DOC-3 (a real fragment of it) |
| seen_holds_agrees | Q | struct | New seen-set scan equals the old one. | refactor-eq |
| spec_hash | Q | struct | The package hash of an import spec is the text before the first `/`. | EZ-HASH-3 |
| pack_ins_le | Q | struct | Inserting a pack that sorts at or before the head puts it first. One step of the insertion sort. | EZ-DOC-2, EZ-DOC-3 (partial) |
| lock_names_hub | Q | refl | `lock.hub(doc(hub, ver, ps)) == hub`. | EZ-DOC-1 (one field) |
| hashes_sorted | C | refl | A two-pack sample is written in hash order. | EZ-DOC-2, EZ-DOC-3 |
| lock_roundtrip | C | refl | A two-pack sample rendered then parsed gives the sorted packs back. | EZ-DOC-1 |
| render_keeps_packages_without_tools | Q | refl | `render.pick` with no tools equals `render`. | EZ-DOC-2 |
| tools_are_not_packages | C | refl | A `[tools.*]` table in the lock does not appear among packs. | EZ-DOC-1 (new: tools are not packages) |
| tool_pin_reads_back | C | refl | A tool's rev rendered into the lock reads back. | EZ-DOC-1 |

**Update:** WP1 of [ez-lock-planner.md](ez-lock-planner.md) puts plain `ez lock` in planner form (`lock/world.bend`, `lock/plan.bend`, `lock/run.bend`) and adds these laws over the planner. The spike's `lock/world/` is deleted; its laws moved here, restated over the planner that `ez lock` now runs, and its list and char lemmas are `check/str.bend`'s (WP0). `root_skips_ez` moved here from ez/LAWS.bend, restated over `P.roots.one`, since the roots are the planner's now. No trail is deleted: the design names none for EZ-DOC-3 or EZ-DOC-5.

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| lock_reproducible | Q | struct | Two Worlds with equal `W.inputs` put the same bytes, or none, at ez.lock.toml. | EZ-DOC-3 (this is the law) |
| clone_reproduces | Q | struct | A World whose trees were read from BEND_LIB puts at ez.lock.toml what the fresh-clone World (`W.reclone`) puts. | EZ-DOC-3 (this is the law) |
| plain_lock_keeps_ledger | Q | struct | A plain lock's plan leaves ez.toml unwritten. | EZ-DOC-5 (this is the law) |
| plain_lock_pins_ledger_sources | Q | struct | Every package a plain lock resolves carries the source ez.toml records for its hash. | EZ-DOC-5 (this is the law) |
| lock_refusal_writes_nothing | Q | struct | A plain lock that refuses plans no write, lay or removal. | EZ-OUT-2 (for a plain lock; untagged until `--upgrade` is planned, WP2) |
| lib_judged_as_clone | Q | struct | A BEND_LIB tree is judged as the same bytes cloned and weighed to the ledger's narHash. | EZ-DOC-3 (supporting) |
| walk_pins_ledger_sources | Q | struct | The walk keeps every resolved package on the ledger's source, by induction on fuel. | EZ-DOC-5 (supporting) |
| root_skips_ez | Q | struct | A tracked path under `.ez/` is never a root. | EZ-DOC-3 (supporting) |
| trim_quoted | Q | struct | eztoml's `trim` leaves a quoted value as it is. | EZ-DOC-1 (supporting, from the spike) |
| strip_quoted | Q | struct | eztoml's `strip` of a quoted value is the value. | EZ-DOC-1 (supporting, from the spike) |

### git/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| origin_read | Q | refl | An origin written by `git.bend` is read back by `lock.bend` as the same source. | EZ-DOC-3 (the origins cache format) |
| among_agrees | Q | struct | New char search equals the old one. | refactor-eq |
| hex_all_agrees | Q | struct | New hex scan equals the old one. | refactor-eq |
| peeled_agrees | Q | struct | New peeled-tag search equals the old one. Decides which commit a tag pins. | refactor-eq (touches EZ-RES-1) |
| is_rev_needs_40 | Q | struct | A ref that is not 40 chars is not a commit. | EZ-RES-1 (tagged) |
| is_rev_needs_hex | Q | struct | 40 chars with a non-hex char is not a commit. | EZ-RES-1 (tagged) |
| is_rev_hex40 | Q | struct | 40 hex chars is a commit, needing no remote. | EZ-RES-1 (tagged) |
| but_drops | Q | struct | Rewriting `origins.toml` drops the table of the given name. | EZ-DOC-3 (origins cache) |
| but_keeps | Q | struct | Rewriting `origins.toml` keeps other tables in order. | EZ-DOC-3 (origins cache) |
| root_rel_here | Q | struct | Recorded `root` when entry and checkout root are at the same depth. | new: recorded root |
| sha256_remote_tip | C | refl | For one `ls-remote --symref` transcript, the tip is the commit row. | EZ-RES-5 |
| sha256_remote_branch | C | refl | For that transcript, the default branch is `main`. | EZ-RES-5 |
| root_rel_up | Q | struct | Recorded `root` when the checkout root is one level above the entry. | new: recorded root |
| choose_release | Q | struct | When any tag is a release, `choose` answers a release. | EZ-RES-1 (tagged) |
| choose_prerelease | Q | struct | With no release, `choose` is `latest` over every tag. | EZ-RES-1 (tagged) |
| branch_of_symref | Q | struct | The default branch is the one HEAD's symref row names. | EZ-RES-1 (tagged) |
| branch_skips_other | Q | struct | A row that is not HEAD's says nothing about the default branch. | EZ-RES-1 (tagged) |
| branch_skips_commit | Q | struct | Nor does HEAD's commit row. | EZ-RES-1 (tagged) |
| exact_skips | Q | struct | A row not named exactly `refs/tags/<ref>`, its `^{}` form, or `refs/heads/<ref>` is never picked. | EZ-RES-1 (tagged) |
| exact_tag_first | Q | struct | A tag of the name is the answer, whatever branch shares it. | EZ-RES-1 (tagged) |
| exact_branch | Q | struct | A branch is the answer only when no tag has the name. | EZ-RES-1 (tagged) |
| latest_greatest | Q | struct | No semver-ish tag in the list is newer, by `ord.ver`, than the one `latest` answers. Key lemma: `ord.ver` read as a `Cmp` is a total preorder (consistent across three versions, flipped when swapped), layer by layer down to `Nat.cmp` and `String.order`. | EZ-RES-1 (tagged) |
| latest_rel_greatest | Q | struct | No release in the list is newer than the one `latest.rel` answers. | EZ-RES-1 (tagged) |
| choose_greatest_release | Q | struct | No release in the list is newer than the tag `choose` answers. | EZ-RES-1 (tagged) |
| choose_greatest_prerelease | Q | struct | With no release, no semver-ish tag is newer than the tag `choose` answers. | EZ-RES-1 (tagged) |
| choose_is_a_tag | Q | struct | A tag `choose` answers is one of the tags in the list. | EZ-RES-1 (tagged) |

### manifest/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| without_idem | Q | struct | Dropping a dep name twice equals dropping it once. | new: `ez remove` idempotent |
| add_idem | Q | struct | `R.add` twice equals once. | new: `ez add` ledger edit idempotent |
| value_first_in_section | Q | struct | A key lookup answers the first value written for it. | new: ledger reading |
| pairs_of_first | Q | struct | A section lookup answers the first section of that name. | new: ledger reading |
| source_of_hub | Q | struct | A dep section with no `git` is a hub dep, and only that decides it. | EZ-RES-4 (supporting) |
| source_of_absent_root | Q | struct | A git section with no `root` has root `.`. | new: ledger reading |
| dep_of_drops_prefix | Q | struct | `[deps.<n>]` is a dep named `n`. | new: ledger reading |
| name_of_sect | Q | refl | A section answers its own name. | new: ledger reading |
| deps_takes_dep_sections | Q | struct | Every `deps.*` section becomes a dep, in document order. | new: ledger reading |
| deps_skips_other_sections | Q | struct | Non-`deps.*` sections are skipped. | new: ledger reading |
| tool_of_drops_prefix | Q | struct | `[tools.<n>]` is a tool named `n`. | new: ledger reading |
| tools_takes_tool_sections | Q | struct | Every `tools.*` section becomes a tool, in order. | new: ledger reading |
| tools_skips_other_sections | Q | struct | Non-`tools.*` sections are skipped. | new: ledger reading |
| tool_needs_no_hash | C | refl | A tool section without `hash` is not reported missing. | new: tools are not packages |
| tool_is_not_a_dep | C | refl | A tool section is not a dep. | new: tools are not packages |
| missing_finds_first | Q | struct | The first `deps.*` section without `hash` is reported by name. | new: ledger validation |
| problem_syntax_first | Q | struct | A syntax error is reported before a missing hash. | new: ledger validation |
| build_is_good | Q | refl | Building from sound sections never fails. | new: ledger validation |
| read_refuses_a_problem | Q | struct | Any problem makes the read `Bad` with that problem. | new: ledger validation |
| parse_reads_the_sections | Q | struct | `M.parse` depends only on the TOML parse's sections and first error. | new: ledger reading |
| show_bad_is_marked | Q | struct | A bad ledger's `show` starts `error: `. | EZ-OUT-1 (adjacent) |
| show_good_opens_with_name | Q | struct | A good ledger's `show` starts with the package name. | none (incidental) |
| find_first | Q | struct | A dep lookup answers the first dep of that name, whole. | new: ledger reading |
| dep_of_unread_is_blank | Q | refl | A bad ledger answers a blank dep for every name. | new: ledger validation |
| rev_of_names_the_commit | Q | struct | `rev_of` answers the rev the git section wrote. | EZ-DOC-5 (supporting) |
| tag_of_names_the_tag | Q | struct | `tag_of` answers the tag the git section wrote. | EZ-DOC-5 (supporting) |
| line_absent | Q | refl | A key with an empty value renders to nothing. | new: ledger rendering |
| source_omits_absent_tag | Q | refl | A git source with no tag writes no `tag` line. | new: ledger rendering |
| dep_opens_its_section | Q | struct | A rendered dep starts `\n[deps.<n>`. | new: ledger rendering |
| tool_opens_its_section | Q | struct | A rendered tool starts `\n[tools.<n>`. | new: ledger rendering |
| deps_splits | Q | struct | Rendering is a list homomorphism over deps. | new: ledger rendering |
| show_opens_with_package | Q | struct | A rendered ledger starts `[package]\n`. | new: ledger rendering |
| render_of_unread_is_blank | Q | refl | A bad ledger renders as `""`. | new: ledger validation (a bad read never overwrites a file) |
| remove_idem | Q | struct | `R.remove` twice equals once. | new: `ez remove` idempotent |
| render_parse_roundtrip | C | refl | One canonical ledger parses and renders back byte for byte. | new: ledger round-trip |
| bolt_is_a_tool | C | refl | In that ledger, `bolt` is a tool. | new: tools are not packages |
| bolt_rev | C | refl | In that ledger, the tool's rev reads back. | new: ledger reading |
| bolt_is_not_a_dep | C | refl | In that ledger, `bolt` is not a dep. | new: tools are not packages |
| sha256_vendor_flag | C | refl | Bare `vendor = true` sets the vendor bit. | EZ-VEN-1 |
| vendor_flag_true | C | refl | `M.flag("true")` is `True`. | EZ-VEN-1 |
| vendor_flag_absent | C | refl | `M.flag("")` is `False`. | EZ-VEN-1 |
| sha256_aims_forward | C | refl | An untagged selected git dep aims at the default branch. | EZ-RES-5 |
| hub_holds | C | refl | A selected hub dep is held. | EZ-RES-4 |
| tag_follows | C | refl | A selected tagged dep re-resolves its tag. | new: tag re-resolution on upgrade |
| unselected_holds | C | refl | An unselected dep is held. | EZ-RES-6 |
| sha256_advances | C | refl | A rev-only pin that is an ancestor of the tip advances to it with no tag. | EZ-RES-5 |
| same_rev_keeps | C | refl | Same rev, same hash is `Keep`. | EZ-DOC-4 (supporting) |
| same_rev_drifts | C | refl | Same rev, different hash is `Drift`. | new: drift refusal |
| tag_moved_off | C | refl | A tag now on a non-descendant commit is `Off`. | new: tag moved off refusal |
| sha256_retarget | C | refl | Retargeting keeps the vendor bit and entry and writes the new rev and hash. | EZ-RES-5, EZ-VEN-1 |
| sha256_allowlist | C | refl | The gitignore allowlist swaps the old hash for the new one. | EZ-VEN-1 |
| imports_follow_hash | C | refl | Import lines naming moved hashes are rewritten; a longer hash, a local import and a comment are left alone. | EZ-VEN-2, EZ-VEN-3 |
| hub_digest_disagrees | C | refl | A "does not hash to" miss is classified as the hub disagreeing. | none |

### net/LAWS.bend

The `net/` module has since moved to ezhttp (#50), which owns these laws. They have left ez's gate, and HTTP correctness is a Trusted row in ez's specification (EZ-TRUST-5 in the RFC). The table records them as they were at `f009e42`.

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| path_absolute | Q | struct | The path a URL splits into starts with `/`. | none (net) |
| utf8_split | Q | struct | `utf8.take` and `utf8.drop` at the same offset partition a string. | none (net) |
| clen_exact | Q | struct | A body of exactly Content-Length bytes comes back whole. | none (net) |
| clen_short | Q | struct | A body shorter than Content-Length is `Torn`. | none (net) |
| take_agrees | Q | struct | New `utf8.take` equals the old one. | refactor-eq |
| drop_agrees | Q | struct | New `utf8.drop` equals the old one. | refactor-eq |
| divide_agrees | Q | struct | New `divide` equals the old one. | refactor-eq |
| hex_agrees | Q | struct | New hex reader equals the old one. | refactor-eq |
| dechunk_agrees | Q | struct | New dechunk equals the old quadratic one. | refactor-eq |
| dechunk_split | Q | struct | Dechunk of `take ++ drop` equals dechunk of the whole. | none (net) |
| split_whole | Q | struct | A string lacking `c` splits into itself. | none (string lemma) |
| split_cut | Q | struct | `split(s ++ c ++ r) == s <> split(r)` when `s` lacks `c`. | none (string lemma) |
| hexlen_ignores_extension | Q | struct | A chunk extension after `;` does not change the length. | none (net) |
| first_is_first_word | Q | struct | `first` of a space split is the first word. | none (net) |
| second_is_next_word | Q | struct | `second` is the first word of what follows. | none (net) |
| request_names_path | Q | struct | The request line is `GET <path>` with the path whole. | none (net) |
| parse_needs_blank_line | Q | struct | A response with no blank line after the head is `Torn`. | none (net) |
| parse_splits_at_blank_line | Q | struct | Head and body split at the first blank line. | none (net) |
| unframed_is_rest | Q | refl | With no framing header the rest is the body. | none (net) |
| head_hit_ignores_case | Q | refl | Header names match case-insensitively. | none (net) |
| parse_needs_status | Q | struct | A head with no status code is `Torn`. | none (net) |
| show_torn_is_marked | Q | struct | `show(Torn)` starts `torn `. | none (incidental) |
| show_reply_opens_with_status | Q | struct | `show(Reply)` starts with the status. | none (incidental) |
| dflt_plain | Q | struct | Any scheme but `https` defaults to port 80. | none (net) |
| dflt_https | C | refl | `https` defaults to 443. | none (net) |
| parse_scheme_first | Q | struct | The scheme is the text before the first colon, lowercased. | none (net) |
| file_empty_host | Q | struct | `file://` with an empty authority has no host and port 80. | none (net) |
| parse_needs_slashes | Q | struct | A URL rest not starting `//` is `Bad`. | none (net) |
| url_show_bad_is_marked | Q | struct | `show(Bad)` starts `bad `. | none (incidental) |
| url_show_opens_with_scheme | Q | struct | `show(Loc)` starts with the scheme. | none (incidental) |

### pub/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| answer_is_a_name | Q | struct | `answer(ls)` is a name exactly when some line of `ls` is. | new: publish reads bend's answer strictly |
| progress_is_not_an_answer | Q | refl | A `publishing ...` line is not a name. | new: publish reads bend's answer strictly |
| import_is_not_an_answer | Q | refl | An `import ...` line is not a name. | new: publish reads bend's answer strictly |
| unread_never_agrees | Q | struct | An answer that is not a name never agrees. | new: publish refuses on disagreement (and EZ-HASH-4) |
| differs_never_agrees | Q | struct | Different hashes never agree. | new: publish refuses on disagreement (and EZ-HASH-4) |
| same_is_agreed | Q | struct | Equal names agree. | new: publish refuses on disagreement |
| clean_is_all_blank | Q | struct | A tree is clean exactly when no porcelain line is non-blank. | new: publish requires a clean tree |
| untracked_is_dirty | Q | refl | `?? path` makes the tree dirty. | new: publish requires a clean tree |
| is_name_needs_0x | Q | struct | A line not starting `0x` is not a name. | new: publish reads bend's answer strictly |
| is_name_needs_length | Q | struct | A line of the wrong length is not a name. | new: publish reads bend's answer strictly |
| is_name_needs_hex | Q | struct | A line with a non-hex digest is not a name. | new: publish reads bend's answer strictly |
| is_name_hex34 | Q | struct | `0x` plus the right number of lowercase hex chars is a name. | new: publish reads bend's answer strictly |
| modified_is_dirty | Q | refl | ` M path` makes the tree dirty. | new: publish requires a clean tree |
| staged_is_dirty | Q | refl | `A  path` makes the tree dirty. | new: publish requires a clean tree |

### ez/LAWS.bend

This file mixes the `ez test` runner, the CLI parser, tool target classification, doctor's drift report, and the progress and error wording. Most of it is closed.

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| nag_needs_prefix | Q | struct | A line not starting `bend ` is not bend's update nag. | none (ez test) |
| report_opens | Q | struct | A line starting `All terms check` opens the check report. | none (ez test) |
| dash_follows_report | Q | struct | A `- ` line right after the report is part of it. | none (ez test) |
| dash_alone_is_output | Q | refl | A `- ` line not after the report is program output. | none (ez test) |
| filter_empty | C | refl | Filtering `""` gives `""`. | none (ez test) |
| filter_old_report | C | refl | The 2.0.16 check report is filtered out. | none (ez test) |
| filter_new_report | C | refl | The 2.0.18 check report and its list are filtered out. | none (ez test) |
| filter_keeps_own_dash | C | refl | A program's own dash line survives. | none (ez test) |
| filter_untouched | C | refl | Output with no report is unchanged. | none (ez test) |
| chomp_trailing | C | refl | Trailing newlines are dropped. | none (ez test) |
| chomp_keeps_inner_blank | C | refl | An inner blank line survives. | none (ez test) |
| want_skips | Q | struct | A non-`#|` line is not a trailer line. | none (ez test) |
| want_keeps | Q | struct | A `#|` line is kept with the prefix dropped. | none (ez test) |
| trailer_extracts | C | refl | The trailer of one sample file. | none (ez test) |
| trailer_empty | C | refl | A file with no trailer wants `""`. | none (ez test) |
| trailer_ignores_note | C | refl | A plain comment is not a trailer. | none (ez test) |
| hash_of_local | Q | struct | A line not starting `import 0x` names no package. | new: doctor drift report |
| hash_of_import | C | refl | One import line names its package. | new: doctor drift report |
| hash_of_relative | C | refl | A relative import names none. | new: doctor drift report |
| imported_dedups | C | refl | The same package imported twice counts once. | new: doctor drift report |
| report_agrees | C | refl | A ledger matching the imports reports no drift. | new: doctor drift report |
| report_both_ways | C | refl | Drift is reported both ways, with fixed wording. | new: doctor drift report |
| report_unused | C | refl | An unused ledger entry is drift, with fixed wording. | new: doctor drift report |
| rel_plain | Q | struct | A path not starting `./` is unchanged by `rel`. | none (ez test) |
| rel_dot | Q | struct | `rel("./" ++ r) == r`. | none (ez test) |
| at_root | C | refl | The shadow's root is `G.root()`. | none (ez test) |
| at_under | Q | struct | A shadow directory sits under the root. | none (ez test) |
| proj_one | C | refl | `./ez/tests/drift.bend` is in project `ez`. | none (ez test) |
| proj_top | C | refl | `./tests/cli.bend` is in no project. | none (ez test) |
| proj_deep | C | refl | `a/b/tests/x.bend` is in project `a/b`. | none (ez test) |
| src_place | C | refl | Aggregate source path for a project. | none (ez test) |
| levels_of_two | C | refl | Shadow levels for two projects. | none (ez test) |
| linked_keeps_bin | C | refl | A directory with no aggregate is linked once. | none (ez test) |
| agg_imports_local | C | refl | The aggregate imports its tests relatively. | none (ez test) |
| agg_calls_behind_mark | C | refl | Each test's main is called behind its marker. | none (ez test) |
| slice_first | C | refl | A test gets the lines behind its marker. | none (ez test) |
| slice_last | C | refl | The last test gets lines to the end. | none (ez test) |
| slice_miss | C | refl | An unreached test gets `""`. | none (ez test) |
| started_yes | C | refl | Output with a marker started. | none (ez test) |
| started_no | C | refl | Output with no marker did not. | none (ez test) |
| headed_line | C | refl | A header line is detected. | none (ez test) |
| headed_quoted | C | refl | A quoted header is not. | none (ez test) |
| solitary_reads_args | C | refl | A test calling `IO.args` runs alone. | none (ez test) |
| solitary_comment_only | C | refl | A comment mentioning it does not. | none (ez test) |
| on_budget | C | refl | `Clock.on("300")` is `True`. | none (ez test) |
| on_zero | C | refl | `Clock.on("0")` is `False`. | none (ez test) |
| on_empty | C | refl | `Clock.on("")` is `False`. | none (ez test) |
| by_effect_keeps | Q | struct | A non-empty deadline passes through. | none (ez test) |
| by_effect_empty | C | refl | No budget is deadline `0`. | none (ez test) |
| rest_empty | C | refl | `Args.rest([]) == []`. | none (CLI) |
| rest_tail | C | refl | `Args.rest` drops the first word. | none (CLI) |
| argv_of_run | C | refl | A `run` line parses as `run` alone. | new: `ez run` forwards args |
| argv_of_other | C | refl | Other lines parse as given. | none (CLI) |
| argv_of_empty | C | refl | An empty line stays empty. | none (CLI) |
| argv_of_tool | C | refl | `tool run T -- a` parses as `tool run T`. | new: `ez tool run` forwards args |
| argv_of_tool_bare | C | refl | `tool run` with no target is kept. | none (CLI) |
| tool_rest_dashes | C | refl | A leading `--` is dropped from forwarded args. | new: `ez tool run` forwards args |
| tool_rest_plain | C | refl | Args after the target forward without `--`. | new: `ez tool run` forwards args |
| target_github | C | refl | `owner/repo` is `https://github.com/owner/repo`, cached as `github.com/owner/repo`. | EZ-RES-3 |
| target_url | C | refl | A URL is kept; `.git` is not in its cache slug. | EZ-RES-3 |
| target_scp | C | refl | `git@host:path` is a URL, cached as `host/path`. | EZ-RES-3 |
| target_abs | C | refl | `/tmp/bolt` is local. | EZ-RES-3 |
| target_file | C | refl | `src/main.bend` is local. | EZ-RES-3 |
| target_dot | C | refl | `./a/b` is local. | EZ-RES-3 |
| target_empty | C | refl | `""` is bad with a fixed reason. | EZ-RES-3 |
| target_escapes | C | refl | A URL whose slug would leave the cache is refused. | new: cache slug cannot escape |
| expand_tilde | C | refl | `~/bolt` expands under home. | EZ-RES-3 |
| expand_plain | C | refl | A non-tilde path is unchanged. | EZ-RES-3 |
| file_bin | C | refl | `bin` is the file built when set. | new: tool build file precedence |
| file_entry | C | refl | With no `bin`, `entry`. | new: tool build file precedence |
| file_default | C | refl | With neither, `main.bend`. | new: tool build file precedence |
| out_name_empty | C | refl | A package with no name links as `app`. | new: tool link name |
| out_name | C | refl | Otherwise the link is the package name. | new: tool link name |
| dep_git_names_the_repo | C | refl | Wording of a git fetch progress line. | none (incidental) |
| dep_hub_names_the_hash | C | refl | Wording of a hub fetch progress line. | none (incidental) |
| dep_cached_is_not_a_fetch | C | refl | Wording of a cache-hit line. | none (incidental) |
| label_from_entry | C | refl | A progress label is the entry's stem. | none (incidental) |
| label_falls_back_to_hash | C | refl | With no entry, the hash. | none (incidental) |
| brief_is_twelve | C | refl | Commits are shown as 12 chars. | none (incidental) |
| brief_keeps_short | C | refl | A shorter name is shown whole. | none (incidental) |
| fetching_names_the_commit | C | refl | Wording of a tool fetch line. | none (incidental) |
| installed_names_the_link | C | refl | Wording of the install success line. | none (incidental) |
| tty_pts | C | refl | `/dev/pts/3` is a terminal. | none (incidental) |
| tty_pipe | C | refl | A pipe is not. | none (incidental) |
| tty_prefers_stderr | C | refl | The spinner prefers stderr's terminal. | none (incidental) |
| tty_falls_back_to_stdout | C | refl | Else stdout's. | none (incidental) |
| tty_neither | C | refl | Else no spinner. | none (incidental) |
| hub_404_teaches | C | refl | Full wording of the hub-404 error. | EZ-OUT-1 (prefix only; the rest is incidental) |
| hub_other_miss_kept | C | refl | Other hub misses keep their reason after `ez: `. | EZ-OUT-1 |
| drift_names_the_tag | C | refl | Full wording of the drifted-tag error. | EZ-OUT-1 (prefix only), new: drift refusal |
| tools_section_is_tools | C | refl | A ledger with `[tools.*]` has tools. | none (hint) |
| deps_are_not_tools | C | refl | A ledger with only deps does not. | none (hint) |
| hint_sync_when_tools | C | refl | Wording of the `sync` hint with tools. | none (incidental) |
| hint_sync_without_tools | C | refl | Wording of the `sync` hint without tools. | none (incidental) |

**Update:** A3 and A6 of [ez-add-planner.md](ez-add-planner.md) add `add_keep_idem`, tagged EZ-LED-2, the untagged `vendor_reads_back`, and four untagged lemmas in `manifest/PROOF.bend` (`find_last.arm`, `find_last`, `revend_again`, `readd_again`). A3 also renders the vendor key bare, `vendor = true`, where ez wrote `vendor = "true"`; `M.flag` reads both. EZ-LED-2 stays pending until `ez add` is in planner form and `add_edits_ledger` (A2) ties the command to `R.add.keep`, when A7 flips it. `vendor_reads_back` fixes the ledger around the dependency and is proved by computation for each bit, so it is two cases rather than a law over ledgers, and it carries no EZ-LED-4 tag.

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| add_keep_idem | Q | struct | `R.add.keep`, the edit `ez add` makes, twice equals once: the second add finds the entry the first wrote (`find_last`), so the vendor bit it keeps is that entry's (`revend_again`), and the rest is `add_idem`. | EZ-LED-2 (the model law; the plan law is A2's) |
| vendor_reads_back | Q | struct | For either bit, a git dependency's vendor bit, in one fixed ledger rendered by `R.show` and parsed back by `M.parse`, is the bit. | none (a check of the bare spelling; EZ-LED-4 needs every ledger) |

## Coverage by RFC requirement

| Requirement | Quantified laws | Closed laws | Status today |
| :---- | :---- | :---- | :---- |
| EZ-HASH-1 | sort_perm, manifest_perm, hash_perm, dedup_dup, dedup_keeps, hash_is_prefix | none | Proved, over file lists with distinct paths. The law is over the file set the import walk produces, not a directory tree. |
| EZ-HASH-2 | none | none (sri_empty_dir only fixes the empty tree) | No law. **Update:** proved by `sha/nar_dir_order_free` (WP8). |
| EZ-HASH-3 | spec_hash (the read side only) | none | Not stated. Nothing relates a vendored tree's directory name to its hash. |
| EZ-HASH-4 | path and header-scan lemmas (supporting) | none | Trusted, as the RFC says. |
| EZ-HASH-5 | none | sri_empty_digest, sri_empty_dir | Trusted, two examples. |
| EZ-HASH-6 | none | hex_empty, hex_abc, hex_manifest | Trusted, three examples. The sha/LAWS.bend header says the digest comes from Giulio2002/bend-sha256 and is proved there against an executable FIPS spec. |
| EZ-DOC-1 | lock_names_hub (one field) | lock_roundtrip, tools_are_not_packages, tool_pin_reads_back | One sample. |
| EZ-DOC-2 | pack_ins_le, render_keeps_packages_without_tools | hashes_sorted | Partial. **Update:** proved by `lock/lock_order_free`, `lock/pack_order_free` and `lock/plain_lock_hashes_distinct` (WP3). |
| EZ-DOC-3 | origin_first, origin_agrees, origin_read, but_drops, but_keeps | hashes_sorted | The resolver's ledger-over-cache rule is proved. The whole-command frame property is not stated. **Update:** proved by `lock/lock_reproducible` and `lock/clone_reproduces` over the planner (WP1). |
| EZ-DOC-4 | none | same_rev_keeps (supporting) | No law. **Update:** proved for a plain lock by `lock/lock_idempotent` and `lock/relock_lays_nothing` over the planner (WP5a); the `--upgrade` half is WP5b. |
| EZ-DOC-5 | rev_of_names_the_commit, tag_of_names_the_tag (supporting) | none | No law about the command. **Update:** proved by `lock/plain_lock_keeps_ledger` and `lock/plain_lock_pins_ledger_sources` over the planner (WP1). |
| EZ-RES-1 | is_rev_* (supporting), peeled_agrees | none | No law about tag selection. **Update:** the decisions are proved over what `git ls-remote` printed, and tagged: `choose_release`, `choose_prerelease`, `choose_greatest_release`, `choose_greatest_prerelease`, `choose_is_a_tag` (with `latest_greatest` and `latest_rel_greatest` under them), `branch_of_symref`, `branch_skips_*`, `exact_*` and `is_rev_*`. Pending until `ez add` asks through the planner (A2 of the add design). |
| EZ-RES-2 | none | none | No law. |
| EZ-RES-3 | none | target_* , expand_* | Examples only. |
| EZ-RES-4 | source_of_hub (supporting) | hub_holds | One example. |
| EZ-RES-5 | none | sha256_aims_forward, sha256_advances, sha256_remote_tip, sha256_remote_branch, sha256_retarget | Examples only. |
| EZ-RES-6 | none | unselected_holds | One example. |
| EZ-VEN-1 | none | sha256_vendor_flag, vendor_flag_true, vendor_flag_absent, sha256_allowlist, sha256_retarget | Examples only. |
| EZ-VEN-2, EZ-VEN-3 | none | imports_follow_hash | One example covering both. |
| EZ-VEN-4 | none | none | No law. |
| EZ-TOOL-1 to EZ-TOOL-6 | none | none | No law. The tool laws that exist are about target classification (EZ-RES-3) and build file choice, which the RFC does not list. |
| EZ-OUT-1 | none | hub_404_teaches, hub_other_miss_kept, drift_names_the_tag | Examples, and they pin the whole message, not the prefix. |
| EZ-TRUST-3 | judge_have, judge_refuse, judge_miss (by `refl`) | hash_match, hash_refuse | ez checks hub bodies against the requested hash itself, so this is not purely trusted. |

## Findings surfaced by the inventory

These come out of reading the laws and the gate that runs them. The findings from reading the command code follow in later sections.

**The proof gate is `ez test`.** `flake.nix` defines `checks.tests = mkProofs { extraFlags = ["--js-only" "--unit-only"]; }`, and `mkProofs` (`nix/lib.nix:183`) runs `ez test`. `ez test` finds every `PROOF.bend` (`ez/test.bend:680`), runs `bend PROOF.bend` on each, and passes a proof only if the first line of output is exactly `All terms check.` (`ez/test.bend:545-558`). That is stricter than the exit status, which is 0 even when bend reports unsafe or foreign defs. So "`bend PROOF.bend` passes" in the RFC currently means "`ez test` saw the bare `All terms check.` line", and the only thing in CI that checks the laws at all is `ez test`. The same run also caches a proof as passed when its key (`C.key("proof", tool, path)`, over the bend version, `$CC`, and the package hash of the proof's import closure) is unchanged. The cache lives in `.ez/cache` in the working directory. `mkProofs` copies a clean source tree into the build, so in CI the cache is always empty and every proof is re-checked; the cache only matters locally. This conflicts with the RFC's position that `ez test` is outside the specification; it needs a decision, which we record as a REVIEW marker in the revised RFC rather than resolve here.

**bolt does not run in CI, and it would fail if it did.** `flake.nix` exposes `checks = { tests; ez; }` with no `mkLint`. The bolt ez pins is v0.4.0 (`24b497e`); current bolt is v0.8.1 (`0b92fbb`), and what follows holds for both unless noted. The `laws` group has three rules: `closed` flags a law in a LAWS.bend with no `for` or `exs` binder, `law` flags a top-level def no law names, and `unsafe` flags an `@unsafe` def a LAWS or PROOF file reaches. ez's `bolt.bend` sets `laws` to `error`, so the 122 closed laws above would each be an error. In the pinned v0.4.0 the `law` rule also exempts any file whose text contains `IO`, which leaves 11 of ez's 37 non-test modules under it; `lock/lock.bend`, `pkg/pkg.bend`, `git/git.bend` and `sha/nar.bend` are exempt. bolt removed that clause in v0.5.0 (bolt#10), and since v0.8.1 fixtures pin it down (bolt#40): a file is exempt only if its path ends in `LAWS.bend` or `PROOF.bend` or contains `tests/`, and IO defs and `main` are graded like any other def. Moving ez's `[tools.bolt]` pin to v0.8.1 therefore puts every module under a law directory under the `law` rule, IO modules included; `run/` and `check/` have no LAWS.bend of their own and stay outside it.

**Update:** `mkLint` is in the flake checks, and `[tools.bolt]` has moved past v0.8.1 and v0.9.0 to the bolt with `trace` (bolt#106), and now pins bolt v1.2.1. There `law` is named `coverage` (L001) and stays at `warn`; `closed` (L002) flags every law with no binder, equality or not, and `trace` (L005) checks `SPEC.md`'s rows against the law tags. ez's `bolt.bend` sets `closed`, `unsafe` and `trace` to `error`, and bolt reports no errors.

**The lock reads a cache.** `lock/origin_agrees` exists because `ez lock` reads `.ez/origins.toml` as well as `ez.toml`. The law proves the ledger wins for any hash the ledger names. It says nothing about a hash only the cache names, which is exactly the fresh-clone case EZ-DOC-3 is about. This is the first input outside ledger plus committed tree, and step 4 traces the rest.

**The 0x hash is over an import closure, not a tree.** `pkg/hash_perm` quantifies over a `List<File>` where `File{at, sum}` is a path and a content digest, gathered by walking local imports and foreign bodies from an entry (`pkg/pkg.bend`). The RFC's "hash of a tree" should be restated in those terms, and the precondition `distinct(xs)` is part of the guarantee.

**Hub bodies are verified by ez.** `hub/judge_*` show ez refuses a hub body whose digest does not start with the requested hash. EZ-TRUST-3 as written ("the hub serves the tree whose hash was requested") is weaker than what ez does; what remains trusted is SHA-256 itself (EZ-HASH-6).

**Some quantified laws are definitional.** 31 quantified laws are proved by `{==}`. `io/write_read` is the clearest case: its comment says a written file reads back, but the statement is `text_of(Some{s}) == s`. A law whose proof is `refl` over open binders is a statement about how a definition unfolds; it can be stated for a requirement, but it protects only against someone changing that definition.

**A large share of ez/LAWS.bend is about `ez test` and wording.** Of its 94 laws, 42 are about the test runner (quiet filter, trailer, shadow layout, clock) and 19 pin progress or error text. Under the RFC's rules, the first group has no requirement to point toward, and the second points toward EZ-OUT-1 only through its prefix.

**Refactor-equivalence laws are a pattern the RFC does not name.** Thirteen laws keep an `old.*` definition beside the new one and prove them equal for all inputs (`net`, `pkg`, `lock`, `git`). They are quantified and they do protect behavior, but they tag no requirement: they say "the rewrite changed nothing", which is the refactoring contract applied once, by hand. The RFC's traceability check would reject them as untagged unless it makes room for them.

## Requirements against code

This section checks each requirement in the RFC draft against what the code does. The verdict is one of: **holds** (the code behaves that way), **partly** (it holds with exceptions listed), or **fails** (the code does not behave that way). Disagreements are recorded here as found. A maintainer has since decided each one; the RFC's "Decided behavior changes" section lists the outcome. Citations are `file:line` at `b28ca2c`.

### Hashing

| ID | Verdict | Evidence |
| :---- | :---- | :---- |
| EZ-HASH-1 | holds, proved | `pkg/pkg.bend:484` hashes `dedup(file.sort(fs))`, so order cannot matter. `pkg/hash_perm` proves it for file lists with distinct paths. The input is the import closure of an entry (`pkg_of`, `pkg/pkg.bend:556`), not a directory tree. With a repeated path and different sums, `dedup` keeps the last of a run and the result depends on order (`pkg/LAWS.bend:52-55` says so). |
| EZ-HASH-2 | holds, not stated | `sha/nar.bend:286-291` lists a directory with `find -printf %f\n` and sorts the names by insertion sort on `String.is_le` (codepoint order, which equals nix's byte order for valid UTF-8). No law states it. **Update:** holds, proved. The serialization is now pure over loaded entries: `sha/nar.bend` loads a directory's children in the order `find` lists them, as `K.File{name, serial}`, and `Nar.dir` sorts them with `K.file.sort` before `Nar.directory` writes them. Every directory's serial goes through `Nar.dir`, and `sha/nar_dir_order_free` proves it independent of the listing order for distinct names. The narHash of every package and tool in ez.lock.toml was recomputed with the new code and matches the recorded one. |
| EZ-HASH-3 | partly | `Git.lay` (`git/git.bend:375-380`) writes `lib/<hash>` where `hash` is ez's own `K.pkg.hash(K.pkg_of(entry))`, and writes the manifest from the same file list, so it holds when written. `place` ignores `cp` failures (`git/git.bend:349-355`). Nothing re-checks a tree later: `read.git` checks files against the on-disk manifest but never the manifest against the directory name, and `restore` accepts a cached tree whose manifest text matches without re-reading files (`lock/restore.bend:121-132`). |
| EZ-HASH-4 | as trusted | `ez publish` compares its hash to `bend --publish`'s answer (`pub/pub.bend:220-251`), but only after bend has uploaded. bend 2.0.25 has no way to report the hash without uploading (`cli_publish` hashes, mines and posts in one step), so this ordering stays. |
| EZ-HASH-5 | as trusted | `Nar.path` (`sha/nar.bend:447`). Known divergences: the exec bit comes from `test -x` (an access check, not the mode bit); the whole `find` output and each symlink target are trimmed, so leading or trailing whitespace in a name or target is lost; a name containing a newline splits in two; submodules are not fetched by ez, while nixpkgs `fetchgit` (used by `nix/lib.nix`) may fetch them. |
| EZ-HASH-6 | fails as worded | `Sha.hex` (`sha/sha.bend:16-17`) hashes each character's codepoint masked to its low byte, with the character count as the length. For ASCII text that is SHA-256 of the bytes; for any other text it is not. The fold is live in ez's own lock: `snap`'s `par.c` holds a non-ASCII character, and its recorded sum is the folded digest, not `sha256sum` of the file. `nix/bend-lib.nix:28-32` documents the fold as Bend's own, so it may be intentional (and required for EZ-HASH-4). `sha/nar.bend` encodes to UTF-8 before hashing, so the two hashes disagree about what a character is. The digest itself comes from Giulio2002/bend-sha256, which its own laws hold to an executable FIPS 180-4 specification. **Update:** the fold was wrong, not Bend's: `bend --publish` hashes UTF-8 bytes. Fixed in the change that made `Sha.hex` hash UTF-8 and re-pinned ezhttp. |

### Ledger and lock documents

| ID | Verdict | Evidence |
| :---- | :---- | :---- |
| EZ-DOC-1 | partly | `Lock.render.tools` (`lock/lock.bend:630`) then `T.parse` and `L.packs` gives back the sorted packs on one example (`lock_roundtrip`). `[lock] bend` and `[lock] version` are never read back. |
| EZ-DOC-2 | unknown (**Update:** proved in WP3, see "Phase three progress") | No law or code path re-renders a parsed lock. eztoml's `T.render` does no escaping, so a value holding `"` would not round-trip. |
| EZ-DOC-3 | fails (**Update:** proved in WP1, see "Phase three progress") | See "What ez lock reads" below. On a fresh clone of this repository, the three non-vendored git dependencies (shake, eztoml, snap) have no tree under `.ez/lib`, `read.git` reads the missing manifest as `""` (`lock/lock.bend:287-293`), and the lock is written with empty `files` tables and exit 0. The committed lock is not reproduced. |
| EZ-DOC-4 | partly | Holds for the lock bytes when the world is unchanged (output is sorted, the old lock is never read). A repeated `--upgrade` re-clones and re-lays every selected pin and rewrites `.ez/origins.toml`. |
| EZ-DOC-5 | holds | Dependency revs are copied from ez.toml (`ledger.put`, `lock/lock.bend:147-153`). `Pin.fill` only fills an empty tool `rev` or `narHash` (`ez/pin.bend:136-149`). Nothing checks that the tree under `.ez/lib` matches the pinned rev. |

### Resolution

| ID | Verdict | Evidence |
| :---- | :---- | :---- |
| EZ-RES-1 | partly | `Git.default.ref` (`git/git.bend:1148-1152`): greatest semver-ish tag, else `main`, else `master`, else `ez: <url> has no main or master`, exit 1. The remote's actual default branch is never asked. "Semver-ish" (`git/git.bend:685-690, 940-998`) is an optional `v`/`V`, one or more dot-separated numeric parts, an optional pre-release, and anything after `+` ignored. The comparator `ord.ver` (`git/git.bend:745-801`) pads missing parts with zero; ties go to the later `ls-remote` row. Pre-releases can win (`v2.0.0-rc1` beats `v1.9.0`). The chosen name is resolved with `ls-remote <url> <ref> refs/tags/<ref>^{}`, which tail-matches, so `main` can resolve to `refs/heads/feature/main`, and a tag sharing a branch's name resolves to the branch. |
| EZ-RES-2 | holds | `git/git.bend:519-579`. A given entry is used as given; otherwise the checkout's `[package] entry`, then `bin`, then `main.bend`; the file must exist (`git/git.bend:470-475`). |
| EZ-RES-3 | partly | `Tgt.classify` (`ez/target.bend:130-179`), shared by `ez add` and `ez tool`. Anything containing `://` or starting `git@` is a URL. `/`, `./`, `../`, `~/` prefixes are paths. Exactly two segments of letters, digits, `-`, `_` are GitHub. Everything else is a path, so `vercel/next.js` and `o/r.git` are paths. `ez add` with a relative path passes it to `git -C .ez/lib/.work-<rev> fetch`, which resolves it against the work directory (`ez/cmd.bend:401-404`). |
| EZ-RES-4 | holds | `aim.src` maps `Hub` to `Hold` (`manifest/upgrade.bend:79-82`). |
| EZ-RES-5 | holds | `aim.tag` empty gives `Forward`, `judge.move` requires ancestry, `retarget` keeps `tag = ""` (`manifest/upgrade.bend:71-76, 104-109, 155-156`). A non-ancestor tip stops with exit 1. |
| EZ-RES-6 | partly | Selection is right (`U.chosen`). Other entries are byte-unchanged only if nothing else in the world changed, because the final `lock.now` recomputes everything. ez.toml is re-rendered whole, which drops comments and unknown keys. A name that is both a dependency and a tool upgrades both. |
| EZ-RES-7 | as trusted | |

### Vendoring and rewriting

| ID | Verdict | Evidence |
| :---- | :---- | :---- |
| EZ-VEN-1 | fails | Only `ez lock --upgrade` writes allowlist lines (`manifest/upgrade.bend:165-218`), and only when a vendored hash moves. `ez add` records `vendor = false` and never writes `.gitignore` (`ez/cmd.bend:371-373`). `ez remove` leaves the line and the tree. `ez init` writes `.ez/`, which makes any `!.ez/lib/<h>` line inert because git cannot re-include under an excluded directory (`ez/cmd.bend:247-248`). |
| EZ-VEN-2 | partly | Lines that start exactly `import 0x<old>/` at column 0 in any `*.bend` outside `.ez` and `.git` are rewritten (`manifest/upgrade.bend:230-254`; `ez/upgrade.bend:350-354`). Indented lines, which the package walk accepts, are not. Swaps apply in sequence, so if one dependency's new hash is another's old one, lines chain. |
| EZ-VEN-3 | partly | Other lines are kept, but the file is split with `String.lines`, rejoined with `\n`, and re-encoded, so invalid UTF-8 elsewhere in a rewritten file can change. Files with no match are not written. |
| EZ-VEN-4 | holds | `ez/doctor.bend` has no file write. Like every command, doctor runs `Env.make()` first, which creates `.ez`, `bin` and the library directory (`ez/main.bend:218-222`, `ez/env.bend:37-41`). |

### Tools

| ID | Verdict | Evidence |
| :---- | :---- | :---- |
| EZ-TOOL-1 | holds | `ez/tool.bend:141-171`. Empty counts as unset. `mkdir -p` result is ignored; a failed `ln` is reported. |
| EZ-TOOL-2 | partly | One file, `<dir>/rev`, records both checkout and binary, written after a successful build (`ez/tool.bend:263-268, 395`). It does not record which file was built or the bend version, so a pinned run with an `entry`/`bin` override and a free run of the same repo at the same rev share a binary. After a failed build `src` holds the new commit and `rev` the old one. |
| EZ-TOOL-3 | holds | Empty rev on a dirty tree (untracked files count) or a non-checkout; `same()` needs a non-empty rev (`ez/tool.bend:244-245, 373-385`). |
| EZ-TOOL-4 | holds | A name in ez.toml `[tools]` takes the lock's rev, url, entry and bin (`ez/tool.bend:555-596`). A remote is `git ls-remote <url> HEAD`. A malformed local ez.toml blocks every tool command, including free `owner/repo` targets. |
| EZ-TOOL-5 | partly | Status is forwarded (`ez/tool.bend:310-330`); signals give 128+N and a failed exec 127, from snap. The program runs with stdin at `/dev/null`, stdout and stderr merged, and its output printed only after it exits. |
| EZ-TOOL-6 | holds | Only `Run` reaches `launch` (`ez/tool.bend:346-353`). Install and upgrade share code and differ only in the final message. |

### Output

| ID | Verdict | Evidence |
| :---- | :---- | :---- |
| EZ-OUT-1 | fails | There is no `ez: <area>:` convention. Forms in use: `ez: <prose>`, `ez: <path or url>: ...`, `ez: git <subcmd>: ...`, `ez: nar hash: ...`, `ez: error: <why>` for ledger failures, Shake's unprefixed `error:` for parse errors, `warning:` on stdout, doctor's `name: problem` lines, and many failures that print a subprocess's output and exit 1 with no ez line. What is consistent is the exit status: every failure ez detects exits 1, except `ez tool run`, which forwards the program's status. |

## What ez lock reads

This is the real `agree_on_inputs` for EZ-DOC-3: every input plain `ez lock` touches, and whether it can change the bytes of `ez.lock.toml`. The path is `Cmd.lock` → `lock.plain` → `Pin.fill` then `lock.now` (`ez/cmd.bend:193-228`), and `lock.now` calls `Lock.lock` → `Lock.lock.at` (`lock/lock.bend:817-834`).

| Input | Tracked? | Changes lock bytes? | Evidence |
| :---- | :---- | :---- | :---- |
| `ez.toml` | yes | yes (sources, tools) | read three times: `ez/pin.bend:352`, `lock/lock.bend:797-806` |
| every `*.bend` under cwd except `./.ez/*` | **no, untracked files included** | yes (which packages appear) | `find . -name *.bend -not -path ./.ez/*`, unsorted, exit status unchecked (`ez/cmd.bend:184-186`); `.claude/` worktrees and nested projects are included |
| local files reached by relative import | usually | yes | `roots` (`lock/lock.bend:498`); a missing file is skipped silently (`:432-446`) |
| `$BEND_LIB/<hash>/manifest` and files, per git-origin package | **no, unless vendored** | yes; a missing tree gives `files = []` and exit 0 | `read.git` (`lock/lock.bend:287-293`) |
| `dirname($BEND_LIB)/origins.toml` (`.ez/origins.toml`) | **no** | yes, for hashes the ledger does not name | `lock/lock.bend:787-790`. A hash only this file names locks as git in a working checkout and falls to Hub on a clone |
| `$BEND_LIB` | env | yes (where trees are read) | `lock/lock.bend:775-778` |
| `$BEND_HUB` | env | yes (`[lock] hub`, and where hub packages come from) | `lock/lock.bend:753-768`; default `https://hub.bend-lang.com`; written even with no hub packages |
| `bend version` (fallback `bend --version`) | toolchain | yes (`[lock] bend`) | `lock/lock.bend:809-812`; a missing bend writes `bend = ""` and exits 0 |
| the hub, over HTTPS, per hub-origin package | network | yes | GET `<hub>/<hash>/manifest` and every file, every run, no cache (`lock/lock.bend:241-255, 320-325`) |
| `git ls-remote`, `git fetch`, NAR walk | network | yes, and **writes ez.toml** | only when a `[tools.*]` pin lacks `rev` or `narHash` (`Pin.fill`, `ez/pin.bend:136-149`) |
| `PATH`, git config, proxies | env | indirectly | which `bend` and `git` run; the HTTP client connects directly and ignores `HTTPS_PROXY` (`net/client.bend:41-44`) |
| cwd | | yes | every path is relative; no search upward for the project root |
| `ez.lock.toml` | yes | no | never read by lock or upgrade |
| clock, `HOME`, `XDG_*`, `.ez/cache` | | no | not on this path |

Under `--upgrade`, `ez lock` also reads `.gitignore`, a second `find` (`-not -path */.ez/* -not -path */.git/*`, `ez/upgrade.bend:352-354`) and the files it lists, remote tags, heads, the HEAD symref, ancestry (via a bare blobless clone and `merge-base --is-ancestor`, `git/git.bend:662-683`), checkouts of each selected dependency and their `ez.toml`, `realpath`, and the hub (`hub.check`, `ez/upgrade.bend:105-108`). It writes ez.toml, `.gitignore`, rewritten sources, `.ez/lib/<hash>` for every selected git dependency (vendored or not), `.ez/origins.toml`, removes old vendored trees, then writes ez.toml again if a tool moved, then the lock (`ez/upgrade.bend:424-431`). The upgrade hard-codes `.ez/lib` (`ez/upgrade.bend:34`) while the final lock reads `$BEND_LIB`. Nothing is rolled back when a later step fails.

What the README's reproducibility sentence ("`ez lock` never has to consult anything a clone does not have") gets right is narrower: dependency `root` and `narHash` are copied from the ledger and never recomputed by plain lock.

**Update:** the decided input changes have landed. At `bec3435` plain `ez lock` reads the ledger, `git ls-files '*.bend'` and those files, trees under `$BEND_LIB` or clones at the ledger rev checked against `narHash`, and hub content, plus any untracked local file a tracked file imports. The planner design for phase three, [ez-lock-planner.md](ez-lock-planner.md), re-traces the inputs and proposes the World that models them. The maintainer accepted that design with every recommendation it made, which adds five behavior changes to the RFC's "Decided behavior changes", rewords EZ-DOC-5 and EZ-RES-6, and adds EZ-OUT-2. Its work packages are how phase three is tracked from here: each lands its requirements' laws and updates this inventory. The trails the design names are already deleted, with every other trail (see the Summary).

### Phase three progress

| WP | State | What landed |
| :---- | :---- | :---- |
| WP0 | done | `check/str.bend`: the spike's list and char lemmas, `string_eq_true`, `split_join`. |
| WP1 | done | Plain `ez lock` in planner form: `lock/world.bend` (the World, `accept`, `inputs`, `reclone`), `lock/plan.bend` (`wants`, `plan`, `step`, `put`, `refuses`, `lockable`), `lock/run.bend` (the interpreter). The IO half of `lock/lock.bend` and the spike are deleted. EZ-DOC-3 and EZ-DOC-5 proved; EZ-OUT-2's law for a plain lock is in, untagged. Behavior changes: no local import is followed, so an untracked file a tracked one imports never reaches the lock; every package is checked against its `0x` name, and a BEND_LIB tree is judged as a clone at the ledger's narHash; a lock that is not `lockable` is refused; a refused lock writes and lays nothing, and a cloned tree is laid under BEND_LIB only by a lock that succeeds. `ez lock --upgrade` keeps its own stages (`Up.run`, `Pin.upgrade`) and then locks through the same planner. |
| WP3 | done | EZ-DOC-2 proved. The lock renders each package as one block of text filed as a `K.File` under its hash and sorts the blocks with `K.file.sort`, so pkg's `sort_perm` gives `lock_order_free` for a package list with distinct hashes, and `pack_order_free` is `sort_perm` under a block. `walk_keeps_hashes_distinct` is the walk invariant, one lemma per step def as for sources, and `plain_lock_hashes_distinct` carries it to `P.packs`, which discharges the premise for every lock the planner writes. `hashes_sorted` was already deleted with the trails. No lock bytes change: this repository's lock round-trips byte for byte. `L.has` now compares the wanted hash first, as pkg's `fresh` does, which changes no answer. |
| WP5a | done | EZ-DOC-4 for a plain lock: `lock/lock_idempotent` (run again on the World it leaves, a plain lock writes the same bytes to ez.lock.toml) and `lock/relock_lays_nothing` (after one that succeeded, no tree arrives by a clone that passes). The World a lock leaves is `after` in `lock/LAWS.bend`: a refused lock leaves the World it read, and one that succeeded leaves every tree it laid read from BEND_LIB with the bytes it was checked with. The proof is `clone_reproduces` read backwards: a clone that passed weighed to the ledger's narHash, so the same bytes from BEND_LIB are judged the same, and the Inputs are unchanged. EZ-DOC-4 stays pending until WP5b proves the `--upgrade` half. |
| WP8 | done | EZ-HASH-2 (`sha/nar_dir_order_free`). |
| WP2, WP4, WP5b, WP6, WP7 | open | |

The demand loop's cost, measured in WP1 on this repository's own lock with every tree already under BEND_LIB (five git packages, all imported directly, so two rounds of `wants` and one `plan`): 0.21 s for the binary before WP1 and 0.53 s after, median of seven runs each. Every round of `wants` scans every tracked source for imports again, since the World holds texts and not scans, and `plan` scans once more and checks every package's SHA-256 once. With every tree to clone (an empty BEND_LIB) the clones dominate: 7.3 s before and 7.4 s after. The design's first risk is real but small; if WP2 makes it matter, the World can carry each source's scanned imports instead of its text.

### Add and remove progress

The design for converting `ez add` and `ez remove`, [ez-add-planner.md](ez-add-planner.md), is accepted with every recommendation. It decides seven behavior changes: a refused `ez add` lays nothing; `ez add` stops writing `.ez/origins.toml`; a re-added vendored dependency is laid under `.ez/lib` and its old committed tree dropped; `ez remove` drops a vendored dependency's committed tree unless another dependency names the same hash; `ez remove` of a name the ledger does not have refuses; a package whose imports climb out of its checkout is refused; and `vendor = true` is written as a bare boolean. EZ-LED-8 now says a leading `~/` is expanded when the path is recorded. Its spike, `pkg/tree/`, makes the package walk a pure function of a checkout's files, computes the same hash as `K.pkg_of` on five entries of this repository, and proves three untagged laws toward EZ-RES-2 and EZ-HASH-3.

| WP | State | Scope |
| :---- | :---- | :---- |
| A0 | open | Shared plan types in `plan/plan.bend`, git questions in `git/ask.bend`, the pure walk promoted and `K.pkg_of` rewritten over it. |
| A1 | open | `ez remove` in planner form. |
| A2 | open | `ez add` in planner form. |
| A3 | open | Bare `vendor = true`. |
| A4 | open | `ez init` in planner form. |
| A5 | done | EZ-RES-1's greatest-release laws in `git/LAWS.bend`: `latest_greatest`, `latest_rel_greatest`, `choose_greatest_release`, `choose_greatest_prerelease`, `choose_is_a_tag`, each over any list with the tag anywhere in it, in the order `ord.ver` gives (numeric parts as numbers, zero-padded; semver pre-release precedence). The existing ref-choice laws are tagged EZ-RES-1. Probing the real binary found no bug in the comparator. The row stays pending until A2 lands `add_pins_chosen` and `add_commit_asks_nothing`. |
| A6 | open | EZ-LED-2 over `Rend.add.keep`. |
| A7 | open | Flip the rows whose halves have all landed. |

## Missing behavior

### Behavior the code guarantees that the RFC does not mention

The ledger model has quantified laws and no requirement: `ez add` and `ez remove` edits are idempotent (`manifest/add_idem`, `remove_idem`, `without_idem`), sections are read first-wins in document order, a ledger that fails to parse is never read into a model and renders as `""` (`read_refuses_a_problem`, `render_of_unread_is_blank`), and a rendered ledger parses back (`render_parse_roundtrip`, closed). A tool section is not a dependency and needs no hash.

`ez publish` refuses a dirty tree (any `git status --porcelain --untracked-files=normal` line, `pub/pub.bend:178-215`) and succeeds only when bend's answer is exactly ez's hash (`pub/pub.bend:51-75, 220-251`). The decision functions are proved (`pub/LAWS.bend`); the ordering is not: the comparison runs after the upload, and stays there because bend 2.0.25 cannot report a package's hash without uploading it.

`ez fetch` checks every restored file against the lock: a hub body's digest must start with the lock's sum, a git file's digest must equal it (`lock/restore.bend:33-89`, `hub/hub.bend:16-17`). It never checks `narHash`, and a cached tree whose manifest text matches is trusted without re-reading files. A missing lock is read as empty and fetch exits 0.

Upgrade refusals: a tag that now names a commit the pin does not descend to stops with exit 1 ("tag X moved off"), and a same-rev pin whose tree no longer hashes to the pin stops with a drift message, exit 1. In the dependency path the drift decision is made by `confirmed` after the new tree and origins entry are already written; `U.judge` is always called with `agree = True` there (`ez/upgrade.bend:221`), so its `Drift` arm is unreachable for dependencies.

Tool build details: the built file is the pin's `bin`, then the pin's `entry`, then the checkout's `bin`, then its `entry`, then `main.bend` (`ez/tool.bend:420-431`); the link name is the checkout's package name, or `app`. A remote slug that is empty, absolute, or contains `..` is refused (`ez/target.bend:85-93`). `ez tool run` forwards the words after the target, dropping one leading `--` (`ez/args.bend:88-89`). `ez tool sync` installs each pin in ledger order at its lock rev and stops at the first failure.

CLI: `ez lock --package X` without `--upgrade` exits 1. A 40-hex ref skips `ls-remote` and records no tag. `ez init` never adds a `.gitignore` rule twice and leaves an existing entry file alone. Every command reads and writes fixed names in the current directory.

### Behavior that looks accidental

Each of these is recorded, not resolved. The RFC carries REVIEW markers for the ones a requirement depends on.

Every command, including `ez help` and a mistyped command, creates `.ez/lib`, `.ez` and `bin` in the current directory (`ez/main.bend:218-222`). `ez init` overwrites an existing ez.toml, losing its dependencies, tools and `bin`. `ez add` names a dependency after its entry's basename minus five characters (`ez/cmd.bend:359-361`), so two packages whose entry is `main.bend` collide, and re-adding a dependency drops `vendor = true`, moves it to the end, and re-renders the whole file. `ez add` vendors before it checks the ledger parses, so a broken ledger leaves trees and origins behind. `ez remove` of an unknown name rewrites the file and exits 0. `ez check`, `build`, `run` and `publish` silently fall back to `main.bend` when the ledger does not parse. `ez build` builds `entry`, not `bin`, and a ledger with an empty `name` builds `bin/.out`. `ez run` does not strip `--` and turns any program failure into exit 1. `ez doctor` fails a project with no dependencies, because the lock grep finds no hashes. README says "Nothing is fetched" for building ez, but only sha256 is vendored; eztoml, snap and shake are not. Comments in `pkg/pkg.bend:4` and `pkg/PROOF.bend:11` cite `tests/publish.sh`, which is `tests/publish.bend`.

The RFC's "Decided behavior changes" picks five of these to fix, in this order, and a sixth was found on the way. Each fix is a pure decision with quantified laws in `ez/LAWS.bend`. The ledger fixes became requirements EZ-LED-6 to EZ-LED-8, and their laws are tagged; the directory and doctor fixes are not requirements.

- [x] `ez init` overwrites an existing ledger. **Fixed:** `Cmd.init.plan` plans no write when `ez.toml` exists, and `ez init` then exits 1 having written nothing, the ignore file and the entry included (`init_keeps_ledger`).
- [x] `ez add` names a dependency after its entry file, so two `main.bend` entries collide, and re-adding a dependency drops `vendor = true`. **Fixed:** `ez/named.bend` names a dependency after its source: a remote by its slug's last component (the repository, `.git` dropped), a path by its directory. A source the ledger already records keeps its name there (`had_keeps`, `had_skips_git`, `had_skips_hub`, `had_fresh`), and a name the ledger gives another source, hub or git, is refused with exit 1 before anything is fetched (`clash_same`, `clash_other`, `clash_hub`, `clash_skips`, `clash_none`); `leaf_is_last` holds the name to what follows the last slash. **Then:** the maintainer put the target's own `[package] name` ahead of the repository and directory names, as cargo does, when it is a TOML bare key (`own_package`, `own_invalid`, `bare_no_dot`, `name_keeps`); the name is then decided once the checkout is read, so a clash leaves the ledger untouched and only the BEND_LIB cache holds the tree. `ez add --rename NAME`, as in cargo, then overrides every rule; a name that is not a bare key is refused before anything is fetched, and so is a second name for a source the ledger already records (`rename_wins`, `rename_dotted`, `rename_moved`, `rename_clash`). `ez add` has no hub target, so no hub dependency is ever named by it. The vendor bit was already kept on a re-add by `Rend.add.keep` (`readd_keeps_vendor`, from the EZ-VEN-1 change); the moved and re-rendered entry is unchanged.
- [x] `ez add` with a relative path fetches relative to the wrong directory. **Fixed:** the ledger keeps the path as it was given, relative to the project, which is the directory ez runs in since every command reads `ez.toml` there, so the lock still reproduces on any clone (EZ-DOC-3). `P.anchor` resolves it against that directory only where git is handed it: `Git.anchored`, called by every git command in `git/git.bend` that takes a source, which covers `ez add`, `ez lock`'s fetch, `ez fetch`, `ez lock --upgrade` and tool pins. A URL and an absolute path are kept as they are. git had read a relative path from `.ez/lib/.work-<rev>` for the fetch, and from the enclosing repository's top level for `ls-remote` (`anchor_url`, `anchor_absolute`, `anchor_relative`).
- [x] Every command, `ez help` included, creates `.ez` and `bin` in the current directory. **Fixed:** `Env.make()` ran before the command line was parsed. `Env.dirs` now names the directories a command writes into without making them itself, `.ez` for `ez check` and `bin` for an `ez build` given no output, and nothing for any other command; every other writer already made its own directory when it wrote (`dirs_other`, `dirs_check`, `dirs_build`, `dirs_build_out`). `ez help`, a mistyped command and `ez doctor` leave an empty directory empty.
- [x] `ez doctor` fails a project with no dependencies. **Fixed:** `Doctor.lock.wrong` counts a lock that names no package as a problem only when the ledger has dependencies, so a fresh `ez init` project, locked or not, passes (`lock_needless`, `lock_needed`, `lock_names`).
- [x] `ez remove` in a directory with no ez.toml creates one and exits 0. This one was found while fixing the others and added to the list. **Fixed:** `Cmd.ledger.of` reads a missing ledger as a refusal for every command that edits one: `ez add`, `ez remove`, and `ez lock` with or without `--upgrade` now exit 1 and write nothing. `ez add` had created a ledger too, and `ez lock` had written a lock of none. `ez fetch` reads only the lock and is unchanged; `ez init` is the one command that makes a ledger (`ledger_missing_unwritten`, `ledger_present_parsed`).

### RFC requirements with no corresponding code

EZ-OUT-1's `ez: <area>:` prefix and structured `Failed{area, reason}` outcome do not exist. No code implements a `World`, a `Plan`, a planner or an interpreter. No code checks that a vendored tree's directory name is the hash of its contents after the tree is written (EZ-HASH-3). EZ-DOC-2's "rendering a parsed lock reproduces the bytes" has no code path that exercises it. No traceability check exists, and bolt reads only `.bend` files, so it cannot read a `SPEC.md` today. **Update:** bolt's `trace` rule (bolt#106, in bolt v1.2.1 as ez pins it) reads `SPEC.md`, and ez runs it at `error`.
