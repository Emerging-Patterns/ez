# AGENTS.md

How to work in this repository. It is written for coding agents, and it holds for people too.

## What ez is

ez is a project manager for Bend 2, written in Bend. Each command is a pure planner (`<cmd>/plan.bend`) over a World (`<cmd>/world.bend`), run by a thin interpreter (`<cmd>/run.bend`). What ez guarantees is listed in `SPEC.md`. The design and its history are in `docs/rfc/ez-spec.md`. The user guide is `docs/guide.md`.

## Build and check

```bash
sh bootstrap.sh
mkdir -p bin
BEND_LIB=$PWD/.ez/lib bend ez/main.bend -o bin/ez.bin
bin/ez.bin prove                     # the proof gate: every PROOF.bend must pass
bin/ez.bin tool run bolt -- --gpu off   # lint: 0 errors
bin/ez.bin lock                      # must leave ez.lock.toml unchanged unless you meant to change it
```

CI runs `nix flake check`, which runs the proof gate and bolt at the lock's `[tools.bolt]` pin, and the `readme` job, which follows the README's install steps.

## Rules

- **Proofs, not tests.** New behavior is backed by quantified laws in a `LAWS.bend`, proved in the sibling `PROOF.bend` and tagged with the requirement ID from `SPEC.md`. bolt's trace rule checks the tags against the Law column. Break each new law once to see the gate catch it, then restore it.
- **Keep the planner pure.** Decisions go in the planner, where laws can reach them. The interpreter only answers questions and runs effects, and what it does is trusted under EZ-TRUST-2.
- **Show a behavior change on the binary.** Reproduce the old behavior with the old build, then show the new one.
- **Never publish to the hub**, not even to test: no real `ez publish` or `bend --publish`. Use `BEND_HUB=http://127.0.0.1:1`, a local fake hub, or a fake `bend`.
- **Never lower bolt levels** or add suppressions to get green.
- **When stuck on a design choice,** compare with cargo or uv and pick the pragmatic option. Record the choice in the RFC.

## Docs

- `SPEC.md` rows and the RFC are written in plain prose. The RFC uses we-voice.
- No em dashes anywhere.
- The README stays short. Reference detail goes in `docs/guide.md`.
- A user-visible change gets a paragraph in the RFC's "Decided behavior changes" and a row in its rollout table. A closed gap comes out of "Known gaps".

## Commits and pull requests

- Commit subjects and PR titles use [Conventional Commits](https://www.conventionalcommits.org): `feat:`, `fix:`, `docs:`, `refactor:`, `chore:`. release-please builds the changelog and the version from them, and PRs are squash-merged under their title.
- One change per PR. Merge only when CI is green.
