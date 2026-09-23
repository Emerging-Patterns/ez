# check: the proofs. `bend PROOF.bend` is the gate. The shared lemma files
# state their laws and prove them in place, and a proof elsewhere imports
# them; this file imports each one so the gate checks it whether or not a proof
# uses it yet.
import Base
import ./eq.bend as Eq
import ./str.bend as Str
import ./toml.bend as Toml
