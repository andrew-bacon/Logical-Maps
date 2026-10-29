import Classicism.Results.MathematicalContingency.CountableRowCoextension
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α σ τ : Type} [Ty α] [Ty σ] [Ty τ]

def RowCovered (I : τ → Prop) (M : τ → (α → Prop) → Prop) (S : α → Prop) : Prop :=
  ∃ a X, I a ∧ M a X ∧ X ≡ S

theorem countable_names_dense_coverage (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rigidN : Rigid (@LowerNat σ _)) (rigidI : Rigid I) (large : ¬ Embeds I (@LowerNat σ _))
    (rc : Classicism.P.RigidComprehension (CountableBitGraph σ τ))
    (C : CountableBitGraph σ τ → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop)
    (cones : PropositionCones (CountableBitCarrier I) (CountableBitOrder I) C P)
    (laws : CountableCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (names : Maps (IndexedName LowerNat I T) I (NameCarrier LowerNat I T))
    (M : τ → (((σ → Prop) → Prop) → Prop) → Prop) (hM : Rigid M)
    (coM : ∀ a X, M a X ↔ IndexedName LowerNat I T a X)
    (S : ((σ → Prop) → Prop) → Prop) (hs : RigidPower LowerNat S)
    (q : Prop) (hnq : q ≠ False) (hqP : EntailmentOrder q P) :
    ∃ r, r ≠ False ∧ EntailmentOrder r q ∧ EntailmentOrder r (RowCovered I M S) := by
  obtain ⟨d,s,hd,hds,hsq⟩ := cones.2.2.2 q hnq hqP
  obtain ⟨e,a,he,ha,hed,hrow⟩ := natural_countableCondition_covers_row (lowerPeano_of_box hi)
    I ConditionBit large rc d hd (CharacteristicBits LowerNat S) (characteristicBits_maps LowerNat S)
  obtain ⟨X,hX,hname⟩ := names.2.1 a ha
  obtain ⟨r,hr,her⟩ := cones.1.2.1 e he
  have hco := countable_whole_row_coext hi I rigidN C T laws total e r he her a X S hname hs hrow
  have covered : EntailmentOrder r (RowCovered I M S) :=
    modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (ha : I a) (hm : M a X) (hc : r → X ≡ S) (hr : r) =>
        (show RowCovered I M S from ⟨a,X,ha,hm,hc hr⟩)))
      (box_elim rigidI.1 a ha)) (box_elim hM.1 a X ((coM a X).mpr hname))) hco
  exact ⟨r,cones.2.1 e r her,entailment_trans r s q
    (cones.2.2.1 d e s r hds her ⟨he,hd,hed⟩) hsq,covered⟩

#classicism_check countable_names_dense_coverage
#classicism_types countable_names_dense_coverage
end Classicism.MathematicalContingency
