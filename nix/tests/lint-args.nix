# mkLint's choice of command, by the bolt the lock pins. bolt 1.65.0 moved
# linting to `bolt check` and made bare `bolt` print its usage and exit 2;
# before it, bare `bolt` linted and `bolt check` wanted files. Each case is a
# `[tools.bolt]` pin and the words mkLint must run after `bolt`. Evaluation
# fails, naming the case, when one is wrong.
{ pkgs, lintArgs }:

let
  cases = [
    { pin = { tag = "v1.27.0"; }; want = [ ]; }
    { pin = { tag = "v1.63.0"; }; want = [ ]; }
    { pin = { tag = "v1.64.0"; }; want = [ ]; }
    { pin = { tag = "v1.65.0"; }; want = [ "check" ]; }
    { pin = { tag = "v1.70.2"; }; want = [ "check" ]; }
    { pin = { tag = "v2.0.0"; }; want = [ "check" ]; }
    { pin = { tag = "1.10.0"; }; want = [ ]; }
    { pin = { rev = "9700daf3a447089a8795d311912014382a74a2a9"; }; want = [ "check" ]; }
    { pin = { tag = "main"; }; want = [ "check" ]; }
    { pin = null; want = [ "check" ]; }
  ];
  wrong = builtins.filter (c: lintArgs c.pin != c.want) cases;
in
if wrong != [ ] then
  throw "lint-args: ${builtins.toJSON (map (c: { inherit (c) pin want; got = lintArgs c.pin; }) wrong)}"
else
  pkgs.runCommand "lint-args" { } "echo ok > $out"
