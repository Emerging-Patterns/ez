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

## Inventory

### sha/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| hex_empty | C | refl | `Sha.hex("")` is the FIPS empty digest. | EZ-HASH-6 |
| hex_abc | C | refl | `Sha.hex("abc")` is the FIPS `abc` vector. | EZ-HASH-6 |
| hex_manifest | C | refl | One fixed manifest line hashes to a fixed digest. | EZ-HASH-6 |
| sri_empty_digest | C | refl | `Nar.sri.hex` of the empty digest is its base64 SRI. | EZ-HASH-5 |
| sri_empty_dir | C | refl | The NAR SRI of an empty directory matches what `nix hash path --sri` prints. | EZ-HASH-5 |

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

### git/LAWS.bend

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| origin_read | Q | refl | An origin written by `git.bend` is read back by `lock.bend` as the same source. | EZ-DOC-3 (the origins cache format) |
| among_agrees | Q | struct | New char search equals the old one. | refactor-eq |
| hex_all_agrees | Q | struct | New hex scan equals the old one. | refactor-eq |
| peeled_agrees | Q | struct | New peeled-tag search equals the old one. Decides which commit a tag pins. | refactor-eq (touches EZ-RES-1) |
| is_rev_needs_40 | Q | struct | A ref that is not 40 chars is not a commit. | EZ-RES-1 (supporting) |
| is_rev_needs_hex | Q | struct | 40 chars with a non-hex char is not a commit. | EZ-RES-1 (supporting) |
| is_rev_hex40 | Q | struct | 40 hex chars is a commit, needing no remote. | EZ-RES-1 (supporting) |
| but_drops | Q | struct | Rewriting `origins.toml` drops the table of the given name. | EZ-DOC-3 (origins cache) |
| but_keeps | Q | struct | Rewriting `origins.toml` keeps other tables in order. | EZ-DOC-3 (origins cache) |
| root_rel_here | Q | struct | Recorded `root` when entry and checkout root are at the same depth. | new: recorded root |
| sha256_remote_tip | C | refl | For one `ls-remote --symref` transcript, the tip is the commit row. | EZ-RES-5 |
| sha256_remote_branch | C | refl | For that transcript, the default branch is `main`. | EZ-RES-5 |
| root_rel_up | Q | struct | Recorded `root` when the checkout root is one level above the entry. | new: recorded root |

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

## Coverage by RFC requirement

| Requirement | Quantified laws | Closed laws | Status today |
| :---- | :---- | :---- | :---- |
| EZ-HASH-1 | sort_perm, manifest_perm, hash_perm, dedup_dup, dedup_keeps, hash_is_prefix | none | Proved, over file lists with distinct paths. The law is over the file set the import walk produces, not a directory tree. |
| EZ-HASH-2 | none | none (sri_empty_dir only fixes the empty tree) | No law. |
| EZ-HASH-3 | spec_hash (the read side only) | none | Not stated. Nothing relates a vendored tree's directory name to its hash. |
| EZ-HASH-4 | path and header-scan lemmas (supporting) | none | Trusted, as the RFC says. |
| EZ-HASH-5 | none | sri_empty_digest, sri_empty_dir | Trusted, two examples. |
| EZ-HASH-6 | none | hex_empty, hex_abc, hex_manifest | Trusted, three examples. The sha/LAWS.bend header says the digest comes from Giulio2002/bend-sha256 and is proved there against an executable FIPS spec. |
| EZ-DOC-1 | lock_names_hub (one field) | lock_roundtrip, tools_are_not_packages, tool_pin_reads_back | One sample. |
| EZ-DOC-2 | pack_ins_le, render_keeps_packages_without_tools | hashes_sorted | Partial. |
| EZ-DOC-3 | origin_first, origin_agrees, origin_read, but_drops, but_keeps | hashes_sorted | The resolver's ledger-over-cache rule is proved. The whole-command frame property is not stated. |
| EZ-DOC-4 | none | same_rev_keeps (supporting) | No law. |
| EZ-DOC-5 | rev_of_names_the_commit, tag_of_names_the_tag (supporting) | none | No law about the command. |
| EZ-RES-1 | is_rev_* (supporting), peeled_agrees | none | No law about tag selection. |
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

These come out of reading the laws and the gate that runs them. The full findings for requirements against code (step 3), the inputs `ez lock` reads (step 4), and missing behavior (step 7) are the next section of this document and are not written yet.

**The proof gate is `ez test`.** `flake.nix` defines `checks.tests = mkProofs { extraFlags = ["--js-only" "--unit-only"]; }`, and `mkProofs` (`nix/lib.nix:183`) runs `ez test`. `ez test` finds every `PROOF.bend` (`ez/test.bend:680`), runs `bend PROOF.bend` on each, and passes a proof only if the first line of output is exactly `All terms check.` (`ez/test.bend:545-558`). That is stricter than the exit status, which is 0 even when bend reports unsafe or foreign defs. So "`bend PROOF.bend` passes" in the RFC currently means "`ez test` saw the bare `All terms check.` line", and the only thing in CI that checks the laws at all is `ez test`. The same run also caches a proof as passed when its key (`C.key("proof", tool, path)`) is unchanged, so a cached pass is trusted rather than re-checked. This conflicts with the RFC's position that `ez test` is outside the specification; it needs a decision, which we record as a REVIEW marker in the revised RFC rather than resolve here.

**bolt does not run in CI.** `flake.nix` exposes `checks = { tests; ez; }`. It does not include `mkLint`, so the bolt `laws` group set to `error` in `bolt.bend` is not enforced by `nix flake check`. Whether it runs elsewhere is part of step 8.

**The lock reads a cache.** `lock/origin_agrees` exists because `ez lock` reads `.ez/origins.toml` as well as `ez.toml`. The law proves the ledger wins for any hash the ledger names. It says nothing about a hash only the cache names, which is exactly the fresh-clone case EZ-DOC-3 is about. This is the first input outside ledger plus committed tree, and step 4 traces the rest.

**The 0x hash is over an import closure, not a tree.** `pkg/hash_perm` quantifies over a `List<File>` where `File{at, sum}` is a path and a content digest, gathered by walking local imports and foreign bodies from an entry (`pkg/pkg.bend`). The RFC's "hash of a tree" should be restated in those terms, and the precondition `distinct(xs)` is part of the guarantee.

**Hub bodies are verified by ez.** `hub/judge_*` show ez refuses a hub body whose digest does not start with the requested hash. EZ-TRUST-3 as written ("the hub serves the tree whose hash was requested") is weaker than what ez does; what remains trusted is SHA-256 itself (EZ-HASH-6).

**Some quantified laws are definitional.** 31 quantified laws are proved by `{==}`. `io/write_read` is the clearest case: its comment says a written file reads back, but the statement is `text_of(Some{s}) == s`. A law whose proof is `refl` over open binders is a statement about how a definition unfolds; it can be stated for a requirement, but it protects only against someone changing that definition.

**A large share of ez/LAWS.bend is about `ez test` and wording.** Of its 94 laws, 42 are about the test runner (quiet filter, trailer, shadow layout, clock) and 19 pin progress or error text. Under the RFC's rules, the first group has no requirement to point toward, and the second points toward EZ-OUT-1 only through its prefix.

**Refactor-equivalence laws are a pattern the RFC does not name.** Thirteen laws keep an `old.*` definition beside the new one and prove them equal for all inputs (`net`, `pkg`, `lock`, `git`). They are quantified and they do protect behavior, but they tag no requirement: they say "the rewrite changed nothing", which is the refactoring contract applied once, by hand. The RFC's traceability check would reject them as untagged unless it makes room for them.
