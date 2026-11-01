# AGENTS.md

How to work in this repository. It is written for coding agents, and it holds for people too.

## What ez is

ez is a project manager for Bend 2, written in Bend. Each command is a pure planner (`src/<cmd>/plan.bend`) over a World (`src/<cmd>/world.bend`), run by a thin interpreter (`src/<cmd>/run.bend`). What ez guarantees is one file per guarantee under `laws/`, imported by the root `LAWS.bend` and proved by the file of the same name under `proofs/`, which the root `PROOF.bend` imports. `docs/SPEC.md` is the requirement table those files replaced, kept as a record the RFCs' IDs point into. The design and its history are in `docs/rfc/ez-spec.md`. The user guide is `docs/guide.md`.

The top-level `main.bend` is ez's program and the entry the hub publishes as `ezx`; it calls `src/ez/app.bend`. Every module lives under `src/`, so the package bend publishes is `main.bend`, the LICENSE beside it and what it imports under `src/`, and `main.bend`'s first line is the hub's description. No file the program reaches may import `LAWS.bend`, `PROOF.bend`, `laws/`, `proofs/`, `src/check/` or `tests/`.

## Build and check

```bash
sh bootstrap.sh
mkdir -p bin
BEND_LIB=$PWD/.ez/lib bend main.bend -o bin/ez.bin
bin/ez.bin prove                     # the proof gate: PROOF.bend must pass
bin/ez.bin tool run bolt --RTS +RTS --gpu off -RTS   # lint: 0 errors
bin/ez.bin lock                      # must leave ez.lock.toml unchanged unless you meant to change it
```

CI runs `nix flake check`, which runs the proof gate and bolt at the lock's `[tools.bolt]` pin, and the `readme` job, which follows the README's install steps.

## Rules

- **Proofs, not tests.** New behavior is backed by quantified laws. Each guarantee is one file, `laws/<Name>.bend`, named for the behavior it guarantees (`LockIdempotent`, `FetchLaysTheLock`), its prose on top and its laws under it; its proofs are `proofs/<Name>.bend`. The root `LAWS.bend` and `PROOF.bend` hold only their imports. Definitions several law files share go in `laws/defs/<Topic>.bend` and lemmas several proofs share in `proofs/lemmas/<Topic>.bend`, each named for what it holds. The file name is the guarantee's identity: no requirement IDs, no tags, no status, and no `LAWS.bend` or `PROOF.bend` in a subdirectory. A law file whose laws prove only part of its guarantee says so in its prose. Break each new law once to see the gate catch it, then restore it.
- **Keep the planner pure.** Decisions go in the planner, where laws can reach them. The interpreter only answers questions and runs effects, and what it does is trusted (the `# Trusted, not proved:` comment in `src/ez/app.bend`). Whatever ez assumes rather than proves is said that way, on the code that assumes it.
- **Show a behavior change on the binary.** Reproduce the old behavior with the old build, then show the new one.
- **Never publish to the hub**, not even to test: no real `ez publish` or `bend --publish`. Use `BEND_HUB=http://127.0.0.1:1`, a local fake hub, or a fake `bend`.
- **Never lower bolt levels** or add suppressions to get green.
- **When stuck on a design choice,** compare with cargo or uv and pick the pragmatic option. Record the choice in the RFC.

## Docs

- Law file prose and the RFC are written in plain prose. The RFC uses we-voice.
- No em dashes anywhere.
- The README stays short. Reference detail goes in `docs/guide.md`.
- A user-visible change gets a paragraph in the RFC's "Decided behavior changes" and a row in its rollout table. A closed gap comes out of "Known gaps".

## Commits and pull requests

- Commit subjects and PR titles use [Conventional Commits](https://www.conventionalcommits.org): `feat:`, `fix:`, `docs:`, `refactor:`, `chore:`. release-please builds the changelog and the version from them, and PRs are squash-merged under their title.
- One change per PR. Merge only when CI is green.
