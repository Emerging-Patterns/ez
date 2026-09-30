# ezx: ez, the package manager for Bend 2.
#
# main: ez's program, and the entry the hub publishes as ezx. Building this
# file builds the `ez` binary (`bend main.bend -o ez`), and a plain Bend file
# that imports it and calls `main` builds the same binary. The program itself
# is src/ez/main.bend; every module it reaches lives under src/, so the
# LICENSE beside this file goes along with the package and nothing else sorts
# before it. ez's ledger library, which reads an ez.toml, is
# src/ledger/manifest.bend, importable from the package at that path.
import Base
import ./src/ez/main.bend as App

# the ez command line: read the words, run the command they name, and exit
# as it ends
def main() -> IO(Unit):
  App.main()
