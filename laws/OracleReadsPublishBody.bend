# How the test hub (src/check/body.bend, for check/oracle.bend) reads the body
# of a publish. This is internal: the oracle stands in for the hub in
# tests/publish.bend and is not part of ez; these laws hold its reading in
# place so a failing publish test is about ez.
#
# Whitespace before a token is skipped and nothing else is. A character that
# must head the text is consumed when it does and refused when it does not. A
# string's span is decoded one character at a time: a character that is not a
# backslash stands for itself, and an empty span decodes to "". A body that
# does not open with `{`, after whitespace, is refused as not an object, and
# nothing of it is read. One file is already in manifest order.
#
# Partly proved: the escapes a backslash introduces, and the reading of the
# `files` object past its brace, are held by the oracle's own refusals (an
# escape or a shape it does not know is refused, never passed through) and by
# tests/publish.bend, not by a law yet.
import Base
import ../src/check/body.bend as B

# LAW: a leading space is skipped
law ws_skips:
  for +ch: Char
  for tail: String
  for space: {True{} == Char.is_space(ch) : Bool}
  {B.ws(SCon{ch, tail}) == B.ws(tail) : String}

# LAW: and the first character that is not one stops the skip, kept
law ws_stops:
  for +ch: Char
  for +tail: String
  for solid: {False{} == Char.is_space(ch) : Bool}
  {B.ws(SCon{ch, tail}) == SCon{ch, tail} : String}

# LAW: a character that heads the text is consumed
law eat_hit:
  for +text: String
  for +ch: Char
  for heads: {True{} == String.starts_with(text, Char.show(ch)) : Bool}
  {B.eat(text, ch) == Some{String.drop(text, 1n)} : Maybe<&2, String>}

# LAW: one that does not is refused
law eat_miss:
  for +text: String
  for +ch: Char
  for absent: {False{} == String.starts_with(text, Char.show(ch)) : Bool}
  {B.eat(text, ch) == None{} : Maybe<&2, String>}

# LAW: an empty span decodes to "", whatever the fuel
law unesc_empty:
  for fuel: Nat
  {B.unesc(fuel, "") == B.UOk{""} : B.Uns}

# LAW: a character that is not a backslash stands for itself, in front of the
# rest of the span decoded
law unesc_plain:
  for fuel: Nat
  for +ch: Char
  for +tail: String
  for plain: {False{} == Char.is_eq(ch, '\\') : Bool}
  {B.unesc(1n+fuel, SCon{ch, tail}) == B.uns.push(ch, B.unesc(fuel, tail)) : B.Uns}

# LAW: a body that does not open with a brace is refused as not an object
law parse_not_object:
  for +body: String
  for open: {None{} == B.eat(B.ws(body), '{') : Maybe<&2, String>}
  {B.parse(body) == B.OBad{"a body that is not an object"} : B.Obj}

# LAW: one file is in manifest order as it is
law sorted_one:
  for entry: B.Ent
  {B.sorted([entry]) == [entry] : List<&2, B.Ent>}
