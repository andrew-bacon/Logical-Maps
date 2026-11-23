import Classicism.Results.MathematicalContingency.DescendingSequences
import Classicism.Results.MathematicalContingency.CountableDirectedUnions

namespace Classicism.MathematicalContingency
variable {σ ν α β γ : Type} [Ty σ] [Ty ν] [Ty α] [Ty β] [Ty γ]

theorem countableDomainCode_graph_coext (N : ν → Prop)
    (R S : α → β → γ → Prop) (C : α → β → ν → Prop)
    (h : CountableDomainCode N R C) (e : ∀ x y z, R x y z ↔ S x y z) :
    CountableDomainCode N S C := by
  refine ⟨?_,?_,h.2.2.1,h.2.2.2⟩
  · intro x y n hc
    obtain ⟨hn,z,hz⟩ := h.1 x y n hc
    exact ⟨hn,z,(e x y z).mp hz⟩
  · intro x y z hz
    exact h.2.1 x y z ((e x y z).mpr hz)

theorem maps_graph_evaluation_coext (N : ν → Prop)
    (A : (α → β → γ → Prop) → Prop)
    (F : ν → (α → β → γ → Prop) → Prop) (hf : Maps F N A)
    (i : ν) (G : α → β → γ → Prop) (hg : F i G) :
    ∀ x y z, G x y z ↔ (∃ H, F i H ∧ H x y z) := by
  intro x y z
  constructor
  · intro h
    exact ⟨G,hg,h⟩
  · intro h
    exact h.elim (fun H hh => (hf.2.2 i H G hh.1 hg) ▸ hh.2)

/-- Closure with the code-space obligation displayed explicitly. -/
theorem countableCondition_countablyClosed_of_codes (hp : LowerPeano σ)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (W : (α → β → ((σ → Prop) → Prop) → Prop) → Prop)
    (K : (α → β → ((σ → Prop) → Prop) → Prop) →
      (α → β → ((σ → Prop) → Prop) → Prop) → Prop)
    (hw : WellOrderOn W K)
    (available : ∀ G, CountableCondition (@LowerNat σ _) A B D G →
      ∃ C, W C ∧ CountableDomainCode LowerNat G C)
    (rc : P.RigidComprehension (α → β → γ → Prop)) :
    @CountablyClosed σ (α → β → γ → Prop) _ _
      (CountableCondition (@LowerNat σ _) A B D) (CountableConditionOrder (@LowerNat σ _) A B D) := by
  intro F hf step
  let R : ((σ → Prop) → Prop) → α → β → γ → Prop :=
    fun i x y z => ∃ G, F i G ∧ G x y z
  have typed : ∀ i, LowerNat i → ∀ x y z, R i x y z → A x ∧ B y ∧ D z := by
    intro i hi x y z h
    exact h.elim (fun G hg => (hf.1 i G hg.1).2.2.1 x y z hg.2)
  have functional : ∀ i, LowerNat i → TernaryFunctional (R i) := by
    intro i hi
    obtain ⟨G,hG,hfG⟩ := hf.2.1 i hi
    exact ternaryFunctional_coext G (R i) hG.2.2.2
      (maps_graph_evaluation_coext LowerNat _ F hf i G hfG)
  have directed : ∀ i j, LowerNat i → LowerNat j → ∃ k, LowerNat k ∧
      TernaryExtends (R k) (R i) ∧ TernaryExtends (R k) (R j) := by
    intro i j hi hj
    obtain ⟨k,G,hk,hG,hiG,hjG⟩ := descending_maps_directed
      (CountableCondition LowerNat A B D) (CountableConditionOrder LowerNat A B D)
      (countableConditionOrder_partialOrder LowerNat A B D) F hf step i j hi hj
    refine ⟨k,hk,?_,?_⟩
    · intro x y z h
      exact h.elim (fun H hh => ⟨G,hG,(hiG H hh.1).2.2 x y z hh.2⟩)
    · intro x y z h
      exact h.elim (fun H hh => ⟨G,hG,(hjG H hh.1).2.2 x y z hh.2⟩)
  have codes : ∀ i, LowerNat i → ∃ C, W C ∧ CountableDomainCode LowerNat (R i) C := by
    intro i hi
    obtain ⟨G,hG,hfG⟩ := hf.2.1 i hi
    obtain ⟨C,hC,hcode⟩ := available G hG
    exact ⟨C,hC,countableDomainCode_graph_coext LowerNat G (R i) C hcode
      (maps_graph_evaluation_coext LowerNat _ F hf i G hfG)⟩
  obtain ⟨S,hS,bound⟩ := countableCondition_directed_lowerBound LowerNat LowerLT
    (lowerNat_wellOrder hp) LowerPair (lowerPair_pairing hp) A B D R typed functional directed W K hw codes rc
  refine ⟨S,hS,?_⟩
  intro i G hG
  exact ⟨hS,(hf.1 i G hG).2,fun x y z h => bound i (hf.1 i G hG).1 x y z ⟨G,hG,h⟩⟩

#classicism_check countableDomainCode_graph_coext maps_graph_evaluation_coext countableCondition_countablyClosed_of_codes
#classicism_types countableDomainCode_graph_coext maps_graph_evaluation_coext countableCondition_countablyClosed_of_codes
end Classicism.MathematicalContingency
