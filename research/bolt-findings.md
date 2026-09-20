# bolt over ez: the findings

ez had never been linted. This is the first pass, against `bolt.bend` at the
repo root with every group set to `error`. Nothing here has been applied.

## How it was run

```
bolt ez/*.bend pkg/*.bend pkg/tests/*.bend manifest/*.bend manifest/tests/*.bend \
     lock/*.bend lock/tests/*.bend net/*.bend net/*/*.bend sha/*.bend sha/tests/*.bend \
     io/*.bend io/*/*.bend run/*.bend run/*/*.bend hub/*.bend check/*.bend tests/*.bend
```

    101 errors, 0 warnings

Two things about the run are load-bearing, and both change what you should
believe about the numbers.

**The installed `bolt` is stale, and it is stale in the rules that matter.**
`/home/noah/.nix-profile/bin/bolt` is bolt 0.3.0. Over the same file set it
prints `70 errors, 0 warnings`, and every one of them is `doc`, `unused` or
`law`. A control file per rule, run through it, shows it implements none of
`concat`, `index`, `eager`, `strict`, `nat`, `escape` or `chars`: each control
comes back `clean`. The same controls through a bolt built from
`/home/noah/projects/bolt` at HEAD fire correctly. So the whole complexity
half of this report exists only because bolt was rebuilt from source into a
scratch path (`bend bolt/main.bend -o <scratch>/bolt.fresh`, bend 2.0.20, no
write into the bolt repo). **Anyone who lints ez with the installed `bolt`
will see 70 findings and none of the four real bugs below.** The bolt repo's
own `bin/bolt.bin` is worse: it answers `clean` to a file with trailing
whitespace, so it should not be used to judge anything.

**bolt descends into hidden directories, which its own `glob.bend` says it
never does.** Run bare in the ez root, the installed bolt reports 1249
findings, 1178 of them inside `.ez/lib/0x0a5c.../` -- the one vendored
third-party package. `bolt/glob.bend`'s `skipped` excludes a name starting
with `.`, and a control directory confirms the installed binary ignores that.
This is a bolt defect, not an ez one; it is why the command above names the
files instead of letting bolt walk. It is also a reason ez would want the
walk fixed before it ever lints itself in anger: `.ez/lib` is vendored code ez
did not write and cannot fix.

## Triage counts

| verdict | count |
|---------|-------|
| real bug (a wrong-scale cost on a real input path) | 4 |
| real smell worth fixing | 93 |
| noise, dismissed with a reason | 4 |

By rule: `law` 59, `eager` 12, `pick` 10, `strict` 8, `doc` 7, `unused` 4,
`concat` 1. The sections below account for all 101 (4 + 4 + 2 + 2 + 2 + 7 +
8 + 7 + 2 + 59 + 4).

No finding produces a wrong answer today, so there is no `BUG` section: every
one of the four real bugs is a performance defect, not a correctness one. The
`divide.go` finding is the closest thing to a correctness issue, because the
code's own comment states the opposite of what the code does.

---

## 1. `concat` and `pick` in `net/http.bend`: dechunking is quadratic (4 findings, real bugs)

This is one defect with four heads, and it is the most consequential thing
bolt found. It sits on the path every `ez fetch` takes when a hub answers with
`Transfer-Encoding: chunked`.

    net/http.bend:135:9: concat: acc grows by appending each step: quadratic
    net/http.bend:49:7:  pick: divide.go recurses in one branch; Bool.pick runs it whatever the condition
    net/http.bend:109:7: pick: utf8.take recurses in one branch
    net/http.bend:119:7: pick: utf8.drop recurses in one branch

### Why it is quadratic

`dechunk(s)` calls `chunks(fuel, divide(s, "\r\n"), "")`, and `chunks` runs
once a chunk. Each step does four things, and three of them walk the whole
remaining body rather than the one chunk:

- **`acc ++ utf8.take(after, n)`** (line 135). `++` on a Bend `String` copies
  its left side. `acc` is every byte decoded so far, so chunk *k* copies
  *k* chunks' worth of bytes. That alone is `O(bytes x chunks)`.
- **`utf8.take(after, n)`** (line 109). The body is
  `Bool.pick(String, Nat.is_lt(n, w), SNil{}, SCon{h, utf8.take(t, ...)})`.
  `Bool.pick` is a function, so the recursive call is evaluated whichever way
  the condition goes. `Nat.sub` saturates at zero, so the recursion does not
  loop, but it does not stop early either: it runs to `SNil`. `utf8.take` of
  `n` bytes out of a string of `m` costs `O(m)`, not `O(n)`, and `after` here
  is the entire rest of the body.
- **`utf8.drop(after, n + 2)`** (line 119). Same shape, same consequence.
- **`divide(rest, "\r\n")`** (line 49), which finds the next chunk header.
  Its own comment says "only when it is not here does the rest of the string
  get looked at, so a hit near the front stops near the front". That is false:
  `divide.push(h, divide.go(t, pat, n))` sits in a `Bool.pick` branch and runs
  whatever `String.starts_with` answered. Every `divide` scans to the end of
  the string, so finding a header two characters in costs the whole remainder.

### Which input makes it bite

A chunked hub response. Take a 4 MB package body in 8 KB chunks: 512 chunks,
each doing `O(4 MB)` of walking for `divide`, `utf8.drop`, `utf8.take` and the
`++`. That is on the order of 2 x 10^9 code-point steps where 4 x 10^6 would
do -- roughly 500x. A 64 KB body in 8 chunks is unnoticeable, which is
presumably why it has never been seen: ez's own tests frame small fixtures
(`check/framing.bend`).

### The fix

Four small, separate rewrites, each provable:

1. `chunks`: carry the pieces as a `List<&2, String>` with `<>` and
   `String.join` once at the end, or prepend and reverse. Removes the `++`.
2. `utf8.take` / `utf8.drop`: bind the recursive call above the pick
   (`+more = utf8.take(t, ...)`) only if you also want it strict -- here you
   do not, so match on the `Bool` in a helper (`Nat.is_lt(n, w)` handed to a
   two-arm `match`) so the stop branch really stops.
3. `divide.go`: same treatment. Hand `String.starts_with(...)` to a helper
   that matches `True{}`/`False{}`, so a header found at position 0 costs one
   comparison, and fix the comment, which currently documents behaviour the
   code does not have.

Doing (2) and (3) alone takes the walk from quadratic to linear; (1) removes
the remaining copy.

---

## 2. `eager` in `pkg/pkg.bend`'s source scanner (4 findings, real smells)

    pkg/pkg.bend:69:10: eager: word runs in both branches
    pkg/pkg.bend:76:14: eager: mod_of runs in both branches
    pkg/pkg.bend:88:40: eager: base_of runs in both branches
    pkg/pkg.bend:88:48: eager: words runs in both branches

`stmt_of` classifies one line of one source file. Line 88 is

    Bool.pick(Stmt, quiet(s), SNone{}, base_of(words(s)))

so `words(s)` -- a `String.split(s, ' ')` plus a filter over the result -- runs
for every blank line and every comment line, the lines `quiet` exists to skip.
`base_of` then always runs `mod_of`, and `mod_of` always runs `word(ws, 1n)`.

This is not quadratic, but it is a constant factor of roughly 3x on a scan ez
performs over every `.bend` file of the project **and** of every package it
resolves, on every `ez lock` and every `ez fetch`. The rule is right and the
fix is the one bolt names: bind the work above the pick, or split the
classification into a `match` on the `Bool` so the skip branch does nothing.

Verdict: real smell, worth fixing, no behaviour change.

## 3. `eager` in `manifest/toml.bend`'s line classifier (2 findings, real smells)

    manifest/toml.bend:142:51: eager: head_of runs in both branches
    manifest/toml.bend:143:50: eager: pair_of runs in both branches

Same shape as (2), one layer down: `line_of` is a four-deep `Bool.pick`
cascade, and both `head_of(s, ...)` and `pair_of(String.split(s, '='))` are
evaluated for every line, including comments and blanks. `String.split` on
every line of `ez.lock.toml` is the measurable part; a lock with fifty
packages is several hundred lines and this parses each of them two or three
times over.

Fix: cascade through a helper that matches on the `Bool`, the way
`head_of` itself already does. Same rewrite as (2).

## 4. `eager` in `pkg/path.bend:133` -- `join` normalises twice (2 findings, real smell)

    pkg/path.bend:133:41: eager: norm runs in both branches
    pkg/path.bend:133:50: eager: norm runs in both branches

    def join(+a: String, +b: String) -> String:
      Bool.pick(String, String.is_empty(a), norm(b), norm(a ++ "/" ++ b))

Both `norm(b)` and `norm(a ++ "/" ++ b)` run every call, so every path join
pays two full component walks and one wasted concatenation. `join` is called
once per import in `lock/lock.bend`'s `root.put`, and through `dir` on every
level of `climb`.

Fix is a one-liner that also reads better: pick the string, then normalise
once.

    norm(Bool.pick(String, String.is_empty(a), b, a ++ "/" ++ b))

## 5. `eager` in `pkg/pkg.bend:470` -- the die path hashes the package first (2 findings, real smell)

    pkg/pkg.bend:470:22: eager: hash_of runs in both branches
    pkg/pkg.bend:470:41: eager: files_of runs in both branches

`pkg.judge` picks between `IO.pure(Pkg, Pkg{hash_of(fs), root, files_of(fs)})`
and `IO.die(...)`. `hash_of` is a sha256 over the whole package manifest, so a
package that escapes its root pays a full hash before it is refused. Wrong
answers are not at risk; a wasted hash on the error path is. Bind the success
value behind the match instead of the pick.

## 6. `pick` with no early exit in searches (7 findings, real smells)

    pkg/pkg.bend:442:7:     pick: escaped recurses in one branch
    net/http.bend:76:7:     pick: hex.go recurses in one branch
    check/oracle.bend:53:7:  pick: ws recurses in one branch
    check/oracle.bend:222:7: pick: str.end recurses in one branch
    check/serve.bend:56:7:   pick: cut recurses in one branch
    check/world.bend:65:7:   pick: starting recurses in one branch
    check/world.bend:73:7:   pick: containing recurses in one branch

Each is a search that cannot stop when it has found what it was looking for.
`escaped` walks every file of a package even after the first escaping path;
`hex.go` consumes the rest of a chunk header after the first non-hex digit
(the header is short, so this is cheap, but the answer is built and thrown
away); the four in `check/` are the test oracle and the fixture server, where
the strings are fixtures.

All real, all the same fix (match on the `Bool` in a helper). Consequence is
bounded in every case: these run over short strings or over lists whose length
is the package's file count. Ranked below the `eager` findings because the
wasted work is proportional to the input, not to the input squared.

## 7. `strict` -- membership tests with no short-circuit (8 findings, real smells)

    ez/doctor.bend:196:30    wrong
    ez/drift.bend:76:32      has
    ez/gate.bend:162:26      started.go
    ez/test.bend:480:35      flag
    pkg/pkg.bend:272:32      seen.has
    manifest/toml.bend:314:28 bare.all
    lock/lock.bend:274:43    has
    lock/lock.bend:388:32    seen.holds

Every one is `Bool.or(<test on the head>, <recurse on the tail>)` (or
`Bool.and` for `bare.all`). `Bool.or` is a function, so both sides run: the
scan always reads the whole list even when the first element answers.

The honest cost is a factor of two on a scan that was already linear, so none
of these is urgent on its own. Two deserve a note. `pkg/pkg.bend:272`
`seen.has` and `lock/lock.bend:388` `seen.holds` are the "have I read this
file already" tests inside the package walk and the project walk; they are
called once per file against a list that grows with every file, so the walk is
already `O(files^2)` and this doubles the constant. On a large repo -- the
thing this report was asked to look for -- that is the second-worst scaling
behaviour in ez, after the http one. It is not quadratic *because* of this
rule, so it is filed as a smell, but the walk itself is worth a separate look:
a sorted structure or a `Map` keyed by path would make it `O(files log files)`.

`manifest/toml.bend:314` `bare.all` is a per-key char walk, bounded by key
length. `ez/`'s four are over argument lists and note lists of a handful of
entries.

## 8. `doc` in `check/eq.bend` (7 findings, real smells)

    check/eq.bend:12,25,45,55,66,87,96: def <name> has no comment above it

Each is the `def` that discharges the `law` immediately above it. bolt exempts
this pattern in a `PROOF.bend` (a law documented in the neighbouring
`LAWS.bend`), and `check/eq.bend` is that pattern under a different filename,
so the exemption misses it. The rule is not wrong -- the file is not a
`PROOF.bend` and bolt cannot know the `law` block above documents the `def`.

Fix: seven one-line comments, or split the file into `check/LAWS.bend` plus
`check/PROOF.bend`, which is what the rest of the repo does. The comments are
cheaper and do not move imports.

## 9. `eager` in `check/` (2 findings, real smells, lowest priority)

    check/framing.bend:67:52: eager: chunked runs in both branches
    check/oracle.bend:350:5:  eager: mem.one.key runs in both branches

`check/framing.bend`'s `reply` builds the whole chunked fixture body for every
request, including requests for `/plain` and `/`. `check/oracle.bend`'s
`mem.one.at` always runs the pair reader even when the object has ended. Both
are test-harness code over fixtures; correct, and slower than they need to be.

## 10. `law` -- 59 pure defs named by no law (59 findings, real smells)

| file | findings |
|------|----------|
| `manifest/manifest.bend` | 16 |
| `manifest/toml.bend` | 14 |
| `pkg/path.bend` | 10 |
| `net/http.bend` | 9 |
| `manifest/render.bend` | 7 |
| `net/url.bend` | 3 |

The rule only applies to a directory that has a `LAWS.bend`, and all four of
`lock/`, `manifest/`, `net/` and `pkg/` do. The distribution is the
interesting part: **`lock/lock.bend` has zero findings and `manifest/` has 37**,
although `lock/LAWS.bend` is the shortest of the four law files (15 lines
against `manifest/LAWS.bend`'s 37). So this is not "bolt wants more laws
everywhere"; it is bolt saying that `manifest/`'s and `net/`'s law files claim
things about a small corner of their modules while `lock/`'s reach theirs.

These are honest findings against ez's own stated convention, not noise. They
are also the largest single piece of work in this report by a wide margin:
closing them means writing laws about a TOML parser and an HTTP framer, which
is real proof work, not a mechanical rewrite. Nothing here blocks anything; it
is a coverage gap in the thing ez says it does.

A cheaper first cut, if the full set is too much: `pkg/path.bend`'s ten are
pure string algebra (`norm`, `join`, `dir`, `base`, `tail`, `ups`, `climb`)
and are the easiest laws in the list to state -- `join(dir(p), base(p)) == p`
and its neighbours.

## 11. `unused` in `pkg/PROOF.bend` (4 findings, dismissed)

    pkg/PROOF.bend:65:21,24,27: parameter f / b / t is never used
    pkg/PROOF.bend:95:22:       parameter h is never used

These are proof defs discharging laws whose parameters are declared erased on
the `law` (`for -f: P.File`). The `def` must take the law's parameter list
positionally whether or not the proof term mentions each one, and erasure is
spelled on the law, not on the def, so there is nothing to delete. Dismissed
as noise.

If silence is wanted, bolt exempts a name starting with `_`, so
`def dedup_keeps.arm(_f, _b, _t, bb)` closes them at zero risk -- and arguably
reads more honestly, since it says out loud that the proof does not look at
them. That is a judgement call for whoever owns `pkg/`, not a fix this report
asks for.

---

## What `bolt.bend` sets, and why

```
correctness  error
suspicious   error
style        error
laws         error
pedantic     unset, so off
```

All four named groups start at `error`, which is what bolt's own `bolt.bend`
does, and nothing was lowered. Every finding above is either a real cost or a
one-line rewrite; the only group with a case for lowering is `laws`, and 59
findings is not a reason -- `lock/` already shows the standard is reachable in
this repo.

`pedantic` is left unset, so `off`, again matching bolt's own config. For the
record, it was measured rather than assumed: turning `pedantic` to `error`
adds **81 `tail` findings** to the 101. `tail` flags a self-call that is not a
tail call in a def whose first live parameter is a `List` or a `String`, and
ez is written almost entirely in that shape, deliberately -- the structural
recursion is what lets Bend's termination checker see through it, which is the
whole reason `lock/lock.bend`'s `pack.sort` is an insertion sort rather than
`List.sort`. Turning it on would ask ez to trade proof for stack depth. bolt's
own README calls the rule "advice that is noisy on idiomatic code". Off.

## Can ez reach `clean`?

Yes, but in two very different pieces.

The 42 non-`law` findings are a week's careful work at most, and every one of
them is a local rewrite with no interface change: bind a call above a
`Bool.pick`, match on a `Bool` instead of picking, build a list and join it
once, add seven comments. The http cluster is the only one that changes
anything a user would notice, and it changes it for the better.

The 59 `law` findings are the real question, and they are a decision about how
far ez wants its own convention to reach, not a lint cleanup. `manifest/` and
`net/` would need laws about a TOML parser and an HTTP framer. That is
achievable -- `lock/` is the proof -- but it is the larger half of the project
by effort.

So: `clean` is reachable. Reaching it in one pass is not realistic, and
`laws` is the axis to stage, not to lower.

## Recommendation: do not gate ez on bolt yet, and here is what would have to change first

ez should be linted by bolt. ez must not *build* or *gate* on bolt.

The build order today is `bend -> ez -> bolt`: ez builds from `bend` and its
one vendored package alone, and bolt is being taught to build with `ez build`.
That DAG is acyclic. Wiring `bolt` into `ez test`, `ez check` or `flake.nix`
closes it into a cycle -- building ez would need bolt, and building bolt would
need ez -- and it would also break the property that a bare clone builds with
no nix, no bun and no devShell. Nothing in this unit touches those files, and
`bolt.bend` is a config file bolt reads; ez never reads it and never invokes
bolt.

For ez to gate on bolt one day, all of the following would have to exist
first:

1. **A prebuilt bolt the gate can fetch, not build.** A binary (or a nix
   output that does not build bolt from source in ez's closure) pinned by
   hash, so `ez test` never compiles bolt. Without this there is no way to
   keep the cycle open.
2. **A bolt whose glob skips hidden directories.** Today bolt 0.3.0 walks into
   `.ez/lib` and files 1178 findings against vendored third-party code ez
   cannot fix. A gate would be red forever on someone else's package.
3. **A released bolt with the complexity rules in it.** The installed 0.3.0
   implements five rules. Gating on it would gate on `doc`, `unused` and
   `law` and miss every finding in sections 1 through 7 of this report, which
   is the wrong half.
4. **The 101 findings closed**, or a `bolt.bend` that stages them honestly.

Until then, linting ez stays what it is here: a person or CI running an
already-built `bolt` against the checked-in `bolt.bend`.
