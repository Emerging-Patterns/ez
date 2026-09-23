# pkg/tree: the laws of the pure package walk spike. The human states them;
# PROOF.bend must prove them. None is tagged with a requirement: nothing runs
# this walk yet, so they prove nothing about `ez add` itself.
# docs/rfc/ez-add-planner.md says which requirement each becomes once the
# planner runs it.
import Base
import ./tree.bend as T
import ../pkg.bend as K

# LAW: an entry the checkout does not hold is refused, and named, whatever
# else the checkout holds and however much fuel the walk has. This is the
# second half of EZ-RES-2 once `ez add` walks with this function: an entry
# that is not in the revision is refused, never hashed as an empty package.
law absent_entry_refused:
  for f: Nat
  for +entry: String
  for +fs: List<&2, T.Source>
  for ne: {False{} == String.is_empty(entry) : Bool}
  for miss: {None{} == T.look(fs, entry) : Maybe<&2, String>}
  {T.of.fuel((1n + f : Nat), entry, fs)
    == T.Refused{"ez: " ++ entry ++ " is imported but not there"} : T.Walked}

# LAW: a walked package is named by the manifest of the very texts it lays.
# The hash is the `0x` name of the files the walk found, each weighed by its
# own text, so a plan that lays `files` under `hash`, with that manifest
# beside them, writes a directory whose name is the digest of its manifest.
# This is EZ-HASH-3's key step for `ez add`.
law walked_named_by_texts:
  for +pre: String
  for +out: List<&2, T.Found>
  {K.hash_of(K.placed(pre, T.found.sums(out)))
    == K.hash_of(T.sums(T.laid(pre, out))) : String}

# LAW: and so the manifest written beside them is the manifest of those texts
law walked_manifest_of_texts:
  for +pre: String
  for +out: List<&2, T.Found>
  {K.manifest_of(K.placed(pre, T.found.sums(out)))
    == K.manifest_of(T.sums(T.laid(pre, out))) : String}
