# Changelog

## [1.2.0](https://github.com/Emerging-Patterns/ez/compare/v1.1.0...v1.2.0) (2026-09-25)


### Bug Fixes

* move the library from manifest/ to ledger/ so ez can go on the hub ([#119](https://github.com/Emerging-Patterns/ez/issues/119)) ([f702841](https://github.com/Emerging-Patterns/ez/commit/f70284165b77a0416a77a649f5ca7ab55e135e4b))

## [1.1.0](https://github.com/Emerging-Patterns/ez/compare/v1.0.0...v1.1.0) (2026-09-25)


### ⚠ BREAKING CHANGES

* **deps:** ez.toml and ez.lock.toml are now written in eztoml 0.4.0's layout (implied [deps]/[packages] headers, bare 0x table names, no blank lines between sections); the next `ez lock` rewrites an old-format lock once. Old-format files still read. ez before 1.1 can fetch and check from a new-format lock, but its doctor calls it out of date and its lock writes the old layout back. Usage errors show the failing command's usage line, and a repeated option (e.g. `--package x --package y`) is refused (shake 0.2.0).

### Features

* **deps:** shake 0.2.0, snap 1.0.0, eztoml 0.4.0, ezhttp 0.5.0, sha256 from the hub ([#118](https://github.com/Emerging-Patterns/ez/issues/118)) ([04bcef8](https://github.com/Emerging-Patterns/ez/commit/04bcef89d63d45b8bb171617a94efc6e9f880091))


### Bug Fixes

* build the fresh check after ez so CI does not run out of memory ([#115](https://github.com/Emerging-Patterns/ez/issues/115)) ([df6d616](https://github.com/Emerging-Patterns/ez/commit/df6d61683c3a20767ad87f89bfa5f446a5075a02))

## [1.0.0](https://github.com/Emerging-Patterns/ez/compare/v0.1.0...v1.0.0) (2026-09-24)


### Features

* ez add &lt;name&gt;@&lt;version&gt; adds a named hub dependency ([#111](https://github.com/Emerging-Patterns/ez/issues/111)) ([052f7e8](https://github.com/Emerging-Patterns/ez/commit/052f7e8edaeeb0cb4578e1b58e3bfb8560dee8e5))
* ez init lays out main.bend and src, and ez publish shows the hub description ([#113](https://github.com/Emerging-Patterns/ez/issues/113)) ([df5f0b9](https://github.com/Emerging-Patterns/ez/commit/df5f0b9174407592be25b31473028596a00605ed))
* ez publish publishes by name with publish-as and version ([#112](https://github.com/Emerging-Patterns/ez/issues/112)) ([edd4448](https://github.com/Emerging-Patterns/ez/commit/edd4448ed80bea0cc04f0e98b4ba6bc5ff953f10))
* ez publish refuses a package whose hub imports are not on the hub ([#114](https://github.com/Emerging-Patterns/ez/issues/114)) ([b566856](https://github.com/Emerging-Patterns/ez/commit/b566856d3e9ac65d49e42ee1be5055092873e606))
* ezx and ez tool run a plain Bend repository, as uvx does ([#108](https://github.com/Emerging-Patterns/ez/issues/108)) ([d5ec51a](https://github.com/Emerging-Patterns/ez/commit/d5ec51a021b80701abb6cf6ecb524fb0e8c4ec05))
* named hub imports, locked by name and hash ([#110](https://github.com/Emerging-Patterns/ez/issues/110)) ([88391e9](https://github.com/Emerging-Patterns/ez/commit/88391e989ea58414b59dc0f5b8204e665bff2183))
