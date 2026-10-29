import Classicism.MathematicalContingency.CohenCardinalCH

/-!
The concrete double-Hartogs coordinate application, with deferred inputs explicit.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Its source proof uses natural_hartogs_coordinate_bounds; its explicit derivation
certificate remains dependency-blocked until that pending certificate is available.
The abbreviation below names an admissible type, not an object-language quantifier.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ γ : Type} [Ty σ] [Ty γ]

abbrev DoubleHartogsNatType (σ : Type) :=
  OrdinalCarrier (OrdinalCarrier ((σ → Prop) → Prop))

set_option synthInstance.maxSize 2000 in
theorem hartogs_cohen_not_cardinalCH (hi : DraftBoxInfinity σ)
    (rc1 : Classicism.P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rp1 : Classicism.P.RigidComprehension
      (OrdinalCarrier ((σ → Prop) → Prop) → OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rc2 : Classicism.P.RigidComprehension (DoubleHartogsNatType σ → Prop))
    (closed : ∀ m, HartogsCarrier (@LowerNat σ _) m →
      Embeds (ClosedSegment (HartogsCarrier (@LowerNat σ _))
        (HartogsOrder (@LowerNat σ _)) m) (@LowerNat σ _))
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ (DoubleHartogsNatType σ)))
    (LC : CohenGraph σ (DoubleHartogsNatType σ) → CohenGraph σ (DoubleHartogsNatType σ) → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ)
    (C : CohenGraph σ (DoubleHartogsNatType σ) → γ → Prop)
    (hH : PartialOrderOn H R)
    (hwC : WellOrderOn (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat σ _)))) LC)
    (hc : DenseCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat σ _))))
      (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat σ _))) ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (Cp : CohenGraph σ (DoubleHartogsNatType σ) → Prop → Prop)
    (T : DoubleHartogsNatType σ → ((σ → Prop) → Prop) → Prop → Prop) (hnP : P ≠ False)
    (cones : PropositionCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat σ _))))
      (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat σ _))) ConditionBit) Cp P)
    (laws : CohenCoordinateLaws (HartogsCarrier (HartogsCarrier (@LowerNat σ _))) Cp T)
    (total : ∀ a n, HartogsCarrier (HartogsCarrier (@LowerNat σ _)) a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, HartogsCarrier (HartogsCarrier (@LowerNat σ _)) a →
      LowerNat n → T a n p → T a n q → p = q)
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)) :
    EntailmentOrder P (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) ∧
      ◇ (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) :=
  cohen_not_cardinalCH_of_coordinate_bounds hi (HartogsCarrier (HartogsCarrier (@LowerNat σ _)))
    rcC LC H R o C hH hwC hc F P hf ho rigidN rcNames rcFreeze Cp T hnP cones laws total functional
    rc ic rcPair icPower rcNamePair
    (natural_hartogs_coordinate_bounds (lowerPeano_of_box hi) rc1 rp1 rc2 closed)

#classicism_check hartogs_cohen_not_cardinalCH
#classicism_types hartogs_cohen_not_cardinalCH
end Classicism.MathematicalContingency
