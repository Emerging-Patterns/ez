# bolt over ez: what was applied

`research/bolt-findings.md` triaged 101 findings against the pre-merge tree
and left them all unapplied. This is the record of acting on it. The report
stays as written; this file says what was done, what was left, and why.

## The run this is measured against

The report was written before six units landed, including a rewrite of
`net/http.bend`, a new `git/` module, a restructured `ez/gate.bend` and
`ez/test.bend`, and changes under `lock/` and `manifest/`. So bolt was run
fresh rather than trusting the report's line numbers, from a bolt built out of
`/home/noah/projects/bolt` at HEAD into a scratch path (the installed 0.3.0
implements none of the rules that find real problems, which the report already
establishes). The file set is every `.bend` in the repo outside `.ez/`, which
now includes `git/` — never linted before — and the two `bench/` trees added
here.

```
137 errors, 0 warnings     before
 78 errors, 0 warnings     after
```

| rule | before | after | what happened |
|--------|-------|-------|---------------|
| `law` | 56 | 51 | five closed by the agreement laws below |
| `unused` | 32 | 21 | the 11 `local u` closed; the 21 left are the dismissed class |
| `strict` | 15 | 0 | all fixed |
| `eager` | 14 | 0 | all fixed |
| `pick` | 11 | 6 | 5 fixed; the 6 left are `old.*` specification defs |
| `doc` | 9 | 0 | all fixed |
| `concat` | 0 | 0 | the report's four real bugs were already fixed on master |

The report's count was 101 against 137 here because `git/` had never been
linted and because the `net/http.bend` rewrite introduced eleven `unused:
local u` findings of its own — the thunk binder the fix is built on.

## The one thing that governs all of it

`Bool.pick` evaluates the branch it does not return. It is an ordinary
function, so both arms are reduced before it chooses, and so are both sides of
`Bool.or` and `Bool.and`. Handing the `Bool` to a small matching def is only
half a repair: an argument is reduced before the def it is passed to can
decline it, so the arm that recurses has to arrive as a thunk
(`rest: Unit -> T`), applied only inside the arm that wants it.
`net/http.bend` and `net/LAWS.bend` are the worked example and every fix here
follows them. The thunk binder is spelled `_u`, which also closes the
`unused` finding the pattern otherwise generates; `net/http.bend` and
`net/PROOF.bend` were renamed to match.

## Fixed: `eager` (14 of 14)

| where | what |
|-------|------|
| `pkg/pkg.bend` `mod_of`, `base_of`, `stmt_of` | the source-file line classifier: `words(s)` ran for every blank and comment line. Now a four-arm cascade. |
| `manifest/toml.bend` `line_of` | the lockfile line classifier: `head_of` and `String.split` ran for every line. Now a four-arm cascade. |
| `pkg/path.bend` `join` | normalised twice and concatenated once for nothing. Now picks the string, then normalises once. |
| `pkg/pkg.bend` `pkg.judge` | a package that escapes its root paid for a full sha256 before being refused. |
| `ez/cmd.bend` `add` | the whole vendor-and-record action was built for a call about to be refused for saying nothing. |
| `git/git.bend` `resolve` | the `git ls-remote` action was built for a ref that was already a commit. |
| `check/framing.bend` `reply` | the whole chunked fixture body was framed for every request. |
| `check/oracle.bend` `mem.one.at` | the pair reader ran even when the object had ended. |

## Fixed: `strict` (15 of 15)

Every one was `Bool.or(<test on the head>, <recurse on the tail>)`, or
`Bool.and` for the two `all` walks, and every one is now a `.step` def that
matches on the head's answer and applies a thunk. `ez/gate.bend`, `lock/`,
`check/world.bend` and `git/git.bend` each had more than one scan of the same
shape, so those share one helper per file (`any.step`, `first.step`,
`among.step`) rather than repeating it.

The two the report singled out are `pkg/pkg.bend`'s `seen.has` and
`lock/lock.bend`'s `seen.holds`: the "have I read this file" tests, called once
per file against a list that grows with every file, so the walk is already
quadratic and this was doubling its constant. The walk itself is still
quadratic — a sorted structure or a `Map` keyed by path is a separate unit and
is **still open**.

## Fixed: `doc` (9 of 9)

The seven proof defs in `check/eq.bend` and the two in `net/bench/dechunk.bend`
have comments now. The file was not split into `LAWS.bend` plus `PROOF.bend`;
the comments are cheaper and move no imports, which is what the report
recommended.

## `pick`: fix or leave, for every one inspected

| where | verdict | why |
|-------|---------|-----|
| `pkg/pkg.bend:442` `escaped` | **fixed** | recursive arm; walks every file of a package past the first escaping path |
| `git/git.bend:120` `peeled` | **fixed** | recursive arm; this is the search that decides which commit a tag pins |
| `check/oracle.bend:53` `ws` | **fixed** | recursive arm over the body of every JSON response the oracle parses |
| `check/oracle.bend:222` `str.end` | **fixed** | recursive arm, and it built a `Succ` over every character past the closing quote |
| `check/serve.bend:56` `cut` | **fixed** | recursive arm over every line of a request body |
| `check/world.bend:65` `starting` | **fixed** | recursive arm; shares `first.step` with `containing` |
| `check/world.bend:73` `containing` | **fixed** | same |
| `net/LAWS.bend:51` `old.take` | **left** | this *is* the pre-rewrite shape, kept as the specification for `take_agrees`. Making it fast would delete the law's content. |
| `net/LAWS.bend:61` `old.drop` | **left** | same |
| `net/LAWS.bend:70` `old.divide.go` | **left** | same |
| `net/LAWS.bend:85` `old.hex.go` | **left** | same |
| `pkg/LAWS.bend:164` `old.escaped` | **left** | new, and for exactly the same reason: it is the specification `escaped_agrees` is stated against |
| `git/LAWS.bend:67` `old.peeled` | **left** | same, for `peeled_agrees` |

Not flagged and deliberately not touched: `hex.of`, `utf8.width`,
`entry.or`, `build.out`, `init.name`, `cc.name`, `probe.flag`, `or_else`,
`words.keep`, `init.missing`, `first`, `key`, `plural`, `lock.note`. Their
arms are literals or cheap projections and nothing recurses, which is the
report's own stopping rule.

## `law`: 5 taken, 51 left

The report is right that 56 `law` findings are a decision about how far ez's
convention reaches and not a lint cleanup, and that closing `manifest/`'s and
`net/`'s means stating laws about a TOML parser and an HTTP framer. That was
not attempted.

What was taken is the other thing: a rewrite that changes a hot function's
shape is where a law earns its place, and `net/LAWS.bend` had already set the
pattern of keeping the pre-rewrite definition under `old.` as the
specification and proving the new one agrees with it on every input. Eleven
such laws were added and all of them discharge:

| file | laws added |
|------|-----------|
| `pkg/LAWS.bend` | `join_agrees`, `stmt_of_agrees`, `escaped_agrees`, `seen_has_agrees` |
| `manifest/LAWS.bend` | `line_of_agrees`, `bare_all_agrees` |
| `lock/LAWS.bend` | `seen_holds_agrees` |
| `git/LAWS.bend` | `among_agrees`, `hex_all_agrees`, `peeled_agrees` |

Between them they closed 5 of the standing `law` findings: three in
`manifest/toml.bend` and two in `pkg/path.bend`.

`line_of_agrees` is not ceremony. The first cut of the `line_of` cascade
dropped the blank-line test, and an empty line would have come back
`LBad{" is neither a section header nor a key"}`. The cascade is written so
the law can be stated over it, and the law is what says the four questions
are still asked in the order the nested picks asked them.

The 51 left are, by file: `manifest/manifest.bend` 16, `manifest/toml.bend`
11, `pkg/path.bend` 8, `manifest/render.bend` 7, `net/http.bend` 6,
`net/url.bend` 3. `lock/lock.bend` still has zero, which is still the argument
that the standard is reachable. **Still open.**

## `unused`: still dismissed

The report's four in `pkg/PROOF.bend` stay dismissed on its own argument, and
no better one turned up: erasure is spelled on the `law`, not on the `def`, so
there is nothing to delete. The class has grown to 21 across
`pkg/`, `net/` and `git/` as those modules gained proofs. The eleven
`unused: local u` findings, which were a different thing — the thunk binder in
`net/http.bend` and `net/PROOF.bend` — are closed by spelling it `_u`, and
every proof arm written here names the parameters it does not look at with a
leading `_` for the same reason. That is the cheap half of the class; the
remaining 21 are all `def`s discharging a `law` whose parameters the law
declares erased.

## Measured, not asserted

Two benchmarks were added, in `bench/` and not `tests/`, following
`net/bench/dechunk.bend` so `ez test` does not collect them. Each carries the
pre-rewrite definition alongside the new one and takes a mode, so the
before-and-after is one binary and one input rather than two builds.

`pkg/bench/scan.bend`, the source-file line classifier, over 200000 blocks of
ten lines, which is two million lines, built native:

```
old 200000    5.06 s
new 200000    3.29 s
```

`manifest/bench/parse.bend`, the lockfile line classifier, over 100000
package stanzas, which is 700000 lines, built native:

```
old 100000    4.53 s
new 100000    2.32 s
```

1.54x and 1.95x. Both modes print the same count, so the classification
happened and was not optimised away. Neither is a wall anyone has hit — these
are constant factors, not the quadratic the `net/http.bend` unit removed — but
both are on paths ez takes on every `ez lock` and every `ez fetch`, and both
rewrites are also the shorter code. Nothing here was kept on a measurement
that did not move.

## The gate

`PASS: 57 / 57`, the baseline, with no test added: everything this unit
changed is either proved by one of the eleven new laws or is test-harness code
the gate already exercises. All five `PROOF.bend` files print exactly
`All terms check.` with no unsafe or foreign annotation.

One trap worth recording for the next person: `check/*.bend` is not reached by
`bend ez/main.bend`, so a linearity error in `check/oracle.bend` compiles
clean at the top level and shows up as `the oracle answers: got no` in
`tests/publish.bend`. Typecheck the `check/` files directly after touching
them.
