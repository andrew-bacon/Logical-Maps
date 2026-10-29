import Classicism.Results.MathematicalContingency.RowRepresentativeMaps
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β]

theorem countable_rows_possible_surjects (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rigidN : Rigid (@LowerNat σ _)) (rigidI : Rigid I) (ndI : DomainND I)
    (large : ¬ Embeds I (@LowerNat σ _))
    (rcGraph : Classicism.P.RigidComprehension (CountableBitGraph σ τ))
    (C : CountableBitGraph σ τ → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop) (nonzero : P ≠ False)
    (cones : PropositionCones (CountableBitCarrier I) (CountableBitOrder I) C P)
    (laws : CountableCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → LowerNat n → T a n p → T a n q → p = q)
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcE : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rcM : Classicism.P.RigidComprehension (τ → (((σ → Prop) → Prop) → Prop) → Prop))
    (R₀ : (((σ → Prop) → Prop) → Prop) → Prop) (hR : Rigid R₀)
    (co : ∀ S, RigidPower LowerNat S ↔ R₀ S)
    (preserved : EntailmentOrder P (∀ S, RigidPower LowerNat S ↔ R₀ S))
    (rcN : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop))) :
    ◇ (∃ F, Surjects F I (RigidPower (@LowerNat σ _))) := by
  have names := countable_names_maps hi I T rigidN rcNames total functional
  obtain ⟨E,M,hE,hM,coE,coM,maps,sub⟩ := indexedNames_frozen_map LowerNat I T rigidI ndI names rcE rcM
  have cover := frozen_rows_cover_preserved_power LowerNat I M P R₀ hR co
    (fun S hs => countable_names_cover_current hi I rigidN rigidI large rcGraph C T P cones laws
      total names M hM coM S hs) preserved
  have hm := rowRepresentatives_necessary_maps LowerNat I E M rcN maps sub
  have hs : EntailmentOrder P (Surjects (RowRepresentatives LowerNat I M) I (RigidPower LowerNat)) :=
    modal_K _ _ (modal_K _ _
      (nec% (fun (hm : Maps (RowRepresentatives LowerNat I M) I (RigidPower LowerNat))
        (hc : P → ∀ S, RigidPower LowerNat S → RowCovered I M S) (hp : P) =>
          rowRepresentatives_surjects LowerNat I M hm (hc hp))) hm) cover
  exact dia_mono P (∃ F, Surjects F I (RigidPower LowerNat))
    (modal_K _ _ (nec% (fun (hs : P → Surjects (RowRepresentatives LowerNat I M) I (RigidPower LowerNat))
      (hp : P) => (show ∃ F, Surjects F I (RigidPower LowerNat) from ⟨RowRepresentatives LowerNat I M,hs hp⟩))) hs) nonzero

theorem countable_completion_possible_surjects (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rigidN : Rigid (@LowerNat σ _)) (rigidI : Rigid I) (ndI : DomainND I)
    (large : ¬ Embeds I (@LowerNat σ _))
    (rcGraph : Classicism.P.RigidComprehension (CountableBitGraph σ τ))
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA B R)
    (cones : DenseCones (CountableBitCarrier I) (CountableBitOrder I) B R o C)
    (incompatible : IncompatibleCones (CountableBitCarrier I) (CountableBitOrder I) B R o C)
    (F : β → Prop → Prop) (P : Prop) (iso : OrderIso F B R (Below P) EntailmentOrder)
    (zero : F o False)
    (R₀ : (((σ → Prop) → Prop) → Prop) → Prop) (hR : Rigid R₀)
    (co : ∀ S, RigidPower LowerNat S ↔ R₀ S)
    (preserved : EntailmentOrder P (∀ S, RigidPower LowerNat S ↔ R₀ S))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcE : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rcM : Classicism.P.RigidComprehension (τ → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcN : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop))) :
    ◇ (∃ G, Surjects G I (RigidPower (@LowerNat σ _))) := by
  obtain ⟨pc,hn,laws,total,functional⟩ := countableCoordinateValue_interfaces I rcGraph B R o C
    cba cones incompatible F P iso zero
  exact countable_rows_possible_surjects hi I rigidN rigidI ndI large rcGraph (RelCompose C F)
    (CountableCoordinateValue I B R C F) P hn pc laws total functional rcNames rcE rcM R₀ hR co preserved rcN

theorem countableBitSetup_possible_surjects
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (limit : StrongLimit K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity σ) (I : τ → Prop) (setup : CountableBitSetup (σ := σ) K L I)
    (rcConditions : Classicism.P.RigidComprehension (CountableBitGraph σ τ → Prop))
    (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA H R)
    (cones : ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (incompatible : ∀ o i, Endpoints H R o i →
      IncompatibleCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (rigidN : Rigid (@LowerNat σ _)) (rigidI : Rigid I) (ndI : DomainND I)
    (large : ¬ Embeds I (@LowerNat σ _))
    (rcGraph : Classicism.P.RigidComprehension (CountableBitGraph σ τ))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rcM : Classicism.P.RigidComprehension (τ → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcN : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice (((σ → Prop) → Prop) → Prop)) :
    ◇ (∃ G, Surjects G I (RigidPower (@LowerNat σ _))) := by
  obtain ⟨P,F,o,i,R₀,he,iso,zero,hn,hR,co,preserved⟩ := countableBitSetup_mp_preserves
    K L mp limit rcK hi I setup rcConditions H R C cba cones rigidN (box_elim rcN) rcFreeze ic
  exact countable_completion_possible_surjects hi I rigidN rigidI ndI large rcGraph H R o C cba
    (cones o i he) (incompatible o i he) F P iso zero R₀ hR co preserved rcNames rcFreeze rcM rcN

#classicism_check countable_rows_possible_surjects countable_completion_possible_surjects countableBitSetup_possible_surjects
#classicism_types countable_rows_possible_surjects countable_completion_possible_surjects countableBitSetup_possible_surjects
end Classicism.MathematicalContingency
