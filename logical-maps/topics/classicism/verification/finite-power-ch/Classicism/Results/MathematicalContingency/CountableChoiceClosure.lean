import Classicism.Results.MathematicalContingency.RelationalChoiceCarriers
import Classicism.Results.MathematicalContingency.CountableSequenceClosure

/-! Finite-Power CH Strategy: domain-code selection from unboxed Relational Choice.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
No well-order of codes and no size witness is used.
-/
namespace Classicism.MathematicalContingency
variable {σ ν α β γ : Type} [Ty σ] [Ty ν] [Ty α] [Ty β] [Ty γ]

theorem uniformDomainCodes_of_relationalChoice (N : ν → Prop)
    (R : ν → α → β → γ → Prop)
    (choice : P.RelationalChoice ν (α → β → ν → Prop))
    (available : ∀ i, N i → CountableDomain N (R i)) :
    ∃ C : ν → α → β → ν → Prop,
      ∀ i, N i → CountableDomainCode N (R i) (C i) := by
  obtain ⟨F,hF,hsub⟩ := relationalChoice_on_carriers N (fun _ => True)
    (fun i C => CountableDomainCode N (R i) C) (fun _ _ _ => False) choice
    (fun i hi => (available i hi).elim (fun C hc => ⟨C,trivial,hc⟩))
  let C : ν → α → β → ν → Prop := fun i x y n => ∃ G, F i G ∧ G x y n
  refine ⟨C,?_⟩
  intro i hi
  obtain ⟨G,_,hg⟩ := hF.2.1 i hi
  apply countableDomainCode_coext N (R i) G (C i) (hsub i G hg)
  intro x y n
  exact ⟨fun h => ⟨G,hg,h⟩,
    fun h => h.elim (fun H hh => (hF.2.2 i H G hh.1 hg) ▸ hh.2)⟩

theorem countableDomain_indexed_union_of_relationalChoice
    (N : ν → Prop) (L : ν → ν → Prop) (hw : WellOrderOn N L)
    (Q : ν → ν → ν → Prop) (hq : PairingOn N Q)
    (R : ν → α → β → γ → Prop)
    (choice : P.RelationalChoice ν (α → β → ν → Prop))
    (available : ∀ i, N i → CountableDomain N (R i)) :
    CountableDomain N (fun x y z => ∃ i, N i ∧ R i x y z) := by
  obtain ⟨C,hC⟩ := uniformDomainCodes_of_relationalChoice N R choice available
  exact countableDomain_indexed_union N L hw Q hq R C hC

theorem countableCondition_directed_lowerBound_of_relationalChoice
    (N : ν → Prop) (L : ν → ν → Prop) (hw : WellOrderOn N L)
    (Q : ν → ν → ν → Prop) (hq : PairingOn N Q)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : ν → α → β → γ → Prop)
    (typed : ∀ i, N i → ∀ x y z, R i x y z → A x ∧ B y ∧ D z)
    (functional : ∀ i, N i → TernaryFunctional (R i))
    (directed : ∀ i j, N i → N j → ∃ k, N k ∧
      TernaryExtends (R k) (R i) ∧ TernaryExtends (R k) (R j))
    (choice : P.RelationalChoice ν (α → β → ν → Prop))
    (available : ∀ i, N i → CountableDomain N (R i))
    (rc : P.RigidComprehension (α → β → γ → Prop)) :
    ∃ S, CountableCondition N A B D S ∧ ∀ i, N i → TernaryExtends S (R i) := by
  have ht : ∀ x y z, (∃ i, N i ∧ R i x y z) → A x ∧ B y ∧ D z := by
    intro x y z ⟨i,hi,h⟩
    exact typed i hi x y z h
  obtain ⟨S,hs,e⟩ := countableCondition_representative N A B D rc
    (fun x y z => ∃ i, N i ∧ R i x y z) ht
    (countableDomain_indexed_union_of_relationalChoice N L hw Q hq R choice available)
    (ternaryFunctional_directed_union N R functional directed)
  exact ⟨S,hs,fun i hi x y z h => (e x y z).mp ⟨i,hi,h⟩⟩

theorem countableCondition_countablyClosed_of_relationalChoice (hp : LowerPeano σ)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (choice : P.RelationalChoice ((σ → Prop) → Prop)
      (α → β → ((σ → Prop) → Prop) → Prop))
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
  have codes : ∀ i, LowerNat i → CountableDomain (@LowerNat σ _) (R i) := by
    intro i hi
    obtain ⟨G,hG,hfG⟩ := hf.2.1 i hi
    exact countableDomain_coext LowerNat G (R i) hG.2.2.1
      (maps_graph_evaluation_coext LowerNat _ F hf i G hfG)
  obtain ⟨S,hS,bound⟩ := countableCondition_directed_lowerBound_of_relationalChoice LowerNat LowerLT
    (lowerNat_wellOrder hp) LowerPair (lowerPair_pairing hp) A B D R typed functional directed choice codes rc
  refine ⟨S,hS,?_⟩
  intro i G hG
  exact ⟨hS,(hf.1 i G hG).2,fun x y z h => bound i (hf.1 i G hG).1 x y z ⟨G,hG,h⟩⟩

#classicism_check uniformDomainCodes_of_relationalChoice countableDomain_indexed_union_of_relationalChoice countableCondition_directed_lowerBound_of_relationalChoice countableCondition_countablyClosed_of_relationalChoice
#classicism_types uniformDomainCodes_of_relationalChoice countableDomain_indexed_union_of_relationalChoice countableCondition_directed_lowerBound_of_relationalChoice countableCondition_countablyClosed_of_relationalChoice
end Classicism.MathematicalContingency
