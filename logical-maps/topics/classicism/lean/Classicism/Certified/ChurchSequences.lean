import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema
import Classicism.Principles.Recursion

/-!
# Checks for Church numerals and sequences

The constructor proof is checked against Classicism's Equivalence gate and
relational type system. The two complete functional recursion results are
stated on the map with mathematical write-ups, not claimed as Lean-certified.
-/

#classicism_audit Classicism.Background.ChurchSequences
#classicism_types_audit Classicism.Background.ChurchSequences

-- A kernel-checked object-language derivation of cons injectivity. Disjointness
-- is checked by the shallow gate and type audit above; it has no translated
-- derivation here (the translator does not normalize its false-valued observation).
set_option maxHeartbeats 0 in
#classicism_derive Classicism.Church.cons_injective
