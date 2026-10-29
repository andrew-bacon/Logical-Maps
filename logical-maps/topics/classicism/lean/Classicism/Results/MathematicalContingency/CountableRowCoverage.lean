import Classicism.Results.MathematicalContingency.CountableRowDensity
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α σ τ : Type} [Ty α] [Ty σ] [Ty τ]

theorem countable_names_cover_current (hi : DraftBoxInfinity σ) (I : τ → Prop)
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
    : EntailmentOrder P (RowCovered I M S) :=
  proposition_density_entailment P (RowCovered I M S)
    (fun q hq hn => countable_names_dense_coverage hi I rigidN rigidI large rc C T P cones laws
      total names M hM coM S hs q hn hq)

theorem frozen_rows_cover_preserved_power (A : α → Prop) (I : τ → Prop)
    (M : τ → (α → Prop) → Prop) (P : Prop) (R₀ : (α → Prop) → Prop)
    (hR : Rigid R₀) (co : ∀ S, RigidPower A S ↔ R₀ S)
    (current : ∀ S, RigidPower A S → EntailmentOrder P (RowCovered I M S))
    (preserved : EntailmentOrder P (∀ S, RigidPower A S ↔ R₀ S)) :
    EntailmentOrder P (∀ S, RigidPower A S → RowCovered I M S) := by
  have old : □ (∀ S, R₀ S → P → RowCovered I M S) :=
    restricted_barcan_unary R₀ (fun S => P → RowCovered I M S) hR
      (fun S hS => current S ((co S).mpr hS))
  exact modal_K _ _ (modal_K _ _
    (nec% (fun (old : ∀ S, R₀ S → P → RowCovered I M S)
      (pres : P → ∀ S, RigidPower A S ↔ R₀ S) (hp : P) S (hS : RigidPower A S) =>
        old S ((pres hp S).mp hS) hp)) old) preserved

#classicism_check countable_names_cover_current frozen_rows_cover_preserved_power
#classicism_types countable_names_cover_current frozen_rows_cover_preserved_power
end Classicism.MathematicalContingency
