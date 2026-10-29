import Classicism.Principles.MathematicalContingency
import Classicism.Results.MathematicalContingency.GoodsellCH

/-! Exact map arrows. Rigidity follows from a boxed RC instance already in
the forcing setup; no additional assumption is inserted.
OpenAI Codex, prompted by Andrew Bacon, 29 October 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.Proofs
open Classicism.P Classicism.MathematicalContingency

theorem bounded_ch_forcing_setup_implies_rigid_lower_nat_e
    {κ : Type} [Ty κ] (setup : P.BoundedCHForcingSetup κ) : P.RigidLowerNatE := by
  obtain ⟨K, L, _, _, _, posRC, _, _, _⟩ := setup
  exact naturalPositiveRC_lowerNat_rigid posRC

theorem bounded_forcing_and_necessary_peano_imply_cardinal_ch_contingency
    {κ : Type} [Ty κ] (setup : P.BoundedCHForcingSetup κ)
    (hi : P.NecessaryLowerPeanoE) : P.CardinalCHContingency := by
  obtain ⟨K, L, posMP, negMP, hInacc, posRC, negRC, completionRC, choice⟩ := setup
  exact (natural_CH_contingency_from_principles
    K L posMP negMP hInacc hi posRC negRC completionRC choice).2

/-- Retain the original, weaker map arrow and its stable identifier. -/
theorem bounded_forcing_and_rigid_naturals_imply_cardinal_ch_contingency
    {κ : Type} [Ty κ] (setup : P.BoundedCHForcingSetup κ)
    (hi : P.NecessaryLowerPeanoE) (_ : P.RigidLowerNatE) : P.CardinalCHContingency :=
  bounded_forcing_and_necessary_peano_imply_cardinal_ch_contingency setup hi

#classicism_check bounded_ch_forcing_setup_implies_rigid_lower_nat_e
  bounded_forcing_and_necessary_peano_imply_cardinal_ch_contingency
  bounded_forcing_and_rigid_naturals_imply_cardinal_ch_contingency
#classicism_types bounded_ch_forcing_setup_implies_rigid_lower_nat_e
  bounded_forcing_and_necessary_peano_imply_cardinal_ch_contingency
  bounded_forcing_and_rigid_naturals_imply_cardinal_ch_contingency
end Classicism.Proofs
