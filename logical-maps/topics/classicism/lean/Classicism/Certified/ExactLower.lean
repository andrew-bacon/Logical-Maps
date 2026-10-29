import Classicism.Certified.ExactLowerSchemas
import Classicism.Results.Records.ExactLower

/-!
# Native object-language certificates for the exact/at-least comparison

The ordinary native translator constructs derivations in Classicism's
object language. Entailment certificates cite those derivations, rather
than treating the shallow Lean propositions as object-language axioms.
This file does not by itself set any map verification status.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

#classicism_derive Classicism.Proofs.necessary_lower_peano_implies_exact_peano_e
#classicism_entails Classicism.Proofs.necessary_lower_peano_implies_exact_peano_e

#classicism_derive Classicism.Proofs.necessary_lower_peano_implies_cardinality_bijection_e
#classicism_entails Classicism.Proofs.necessary_lower_peano_implies_cardinality_bijection_e

#classicism_derive Classicism.Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e
#classicism_entails Classicism.Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e

#print axioms Classicism.Proofs.necessary_lower_peano_implies_exact_peano_e.derivable
#print axioms Classicism.Proofs.necessary_lower_peano_implies_exact_peano_e.entails
#print axioms Classicism.Proofs.necessary_lower_peano_implies_cardinality_bijection_e.derivable
#print axioms Classicism.Proofs.necessary_lower_peano_implies_cardinality_bijection_e.entails
#print axioms Classicism.Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e.derivable
#print axioms Classicism.Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e.entails

open Lean Elab Command in
run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for name in [
      `Classicism.Proofs.necessary_lower_peano_implies_exact_peano_e.derivable,
      `Classicism.Proofs.necessary_lower_peano_implies_exact_peano_e.entails,
      `Classicism.Proofs.necessary_lower_peano_implies_cardinality_bijection_e.derivable,
      `Classicism.Proofs.necessary_lower_peano_implies_cardinality_bijection_e.entails,
      `Classicism.Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e.derivable,
      `Classicism.Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e.entails] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all allowed.contains do
      throwError "Unexpected axiom in {name}: {axioms}"
    logInfo m!"Native exact/lower certificate audited: {name}; axioms = {axioms}"
