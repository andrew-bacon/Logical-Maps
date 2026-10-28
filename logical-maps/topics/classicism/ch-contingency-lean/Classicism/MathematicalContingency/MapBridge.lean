import Classicism.MathematicalContingency.ClosedBoundsCH

/-!
# Exact Logical-Maps bridge for checkpoint 140

The original closed-bounds theorem and its object-language certificate
are in `ClosedBoundsCH.lean` and `Certificates/ClosedBoundsCH01.lean`.
This wrapper makes the finite instance bundle explicit and projects the
cardinal-CH conclusion. It adds NO rigidity derivation or axiom.

It is a *source-level bridge*, not yet a `Classicism.Map` certificate.
The Logical-Maps map entry remains `certificate.lean: none` until its
own `pmap lean-check classicism --update` has been run successfully.

OpenAI GPT-6, prompted by Andrew Bacon, 28 October 2026.
-/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper

/-- The exact finite package of non-numerical premises for the
    checkpoint-140 endpoint, leaving `DraftBoxInfinity e` and
    `Rigid LowerNat` as separate hypotheses.  The two `MPAt`
    instances share a single size witness K,L. -/
def BoundedCHForcingSetup (κ : Type) [Ty κ] : Prop :=
  ∃ (K : κ → Prop) (L : κ → κ → Prop),
    MPAt (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop) K L ∧
    MPAt (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) K L ∧
    StronglyInaccessible K L ∧
    NaturalPositiveRC (κ := κ) ∧
    NaturalNegativeRC (κ := κ) ∧
    □ (P.RigidComprehension
      (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)) ∧
    NaturalCHChoice

/-- Contingency of the cardinal formulation of CH, and *not* the
    structural assertion about complete ordered fields. -/
def CardinalCHContingency : Prop :=
  (◇ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _)))) ∧
  (◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))))

/-- A shallow consequence of the checkpoint-140 conditional theorem.
    The only extra natural-number premise is `Rigid LowerNat`; it is
    *not* derived here.  This bridge has not been separately compiled
    or translated by the map's certification toolchain. -/
theorem bounded_forcing_implies_cardinal_ch_contingency
    {κ : Type} [Ty κ]
    (setup : BoundedCHForcingSetup κ)
    (hi : DraftBoxInfinity e)
    (rigidN : Rigid (@LowerNat e _)) : CardinalCHContingency := by
  obtain ⟨K, L, posMP, negMP, hInacc, posRC, negRC, completionRC, choice⟩ := setup
  exact (natural_CH_contingency_closedBounds
    K L posMP negMP hInacc hi posRC negRC completionRC choice rigidN).2

#classicism_check bounded_forcing_implies_cardinal_ch_contingency
#classicism_types bounded_forcing_implies_cardinal_ch_contingency
end Classicism.MathematicalContingency
