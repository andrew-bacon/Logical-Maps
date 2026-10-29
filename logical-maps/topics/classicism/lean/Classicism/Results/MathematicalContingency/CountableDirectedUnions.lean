import Classicism.Results.MathematicalContingency.CountableDomainFamilies

/-! A directed family of compatible partial functions has a functional union.
Well-ordered domain-code availability supplies a countable rigid lower bound.
The code-space hypotheses are explicit obligations, not additional deferrals. -/
namespace Classicism.MathematicalContingency
variable {ν α β γ : Type} [Ty ν] [Ty α] [Ty β] [Ty γ]

theorem ternaryFunctional_directed_union (N : ν → Prop)
    (R : ν → α → β → γ → Prop)
    (functional : ∀ i, N i → TernaryFunctional (R i))
    (directed : ∀ i j, N i → N j → ∃ k, N k ∧
      TernaryExtends (R k) (R i) ∧ TernaryExtends (R k) (R j)) :
    TernaryFunctional (fun x y z => ∃ i, N i ∧ R i x y z) := by
  intro x y z w hz hw
  obtain ⟨i,hi,hz⟩ := hz
  obtain ⟨j,hj,hw⟩ := hw
  obtain ⟨k,hk,hki,hkj⟩ := directed i j hi hj
  exact functional k hk x y z w (hki x y z hz) (hkj x y w hw)

theorem countableCondition_directed_lowerBound
    (N : ν → Prop) (L : ν → ν → Prop) (hw : WellOrderOn N L)
    (Q : ν → ν → ν → Prop) (hq : PairingOn N Q)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : ν → α → β → γ → Prop)
    (typed : ∀ i, N i → ∀ x y z, R i x y z → A x ∧ B y ∧ D z)
    (functional : ∀ i, N i → TernaryFunctional (R i))
    (directed : ∀ i j, N i → N j → ∃ k, N k ∧
      TernaryExtends (R k) (R i) ∧ TernaryExtends (R k) (R j))
    (W : (α → β → ν → Prop) → Prop)
    (K : (α → β → ν → Prop) → (α → β → ν → Prop) → Prop)
    (hk : WellOrderOn W K)
    (available : ∀ i, N i → ∃ F, W F ∧ CountableDomainCode N (R i) F)
    (rc : P.RigidComprehension (α → β → γ → Prop)) :
    ∃ S, CountableCondition N A B D S ∧ ∀ i, N i → TernaryExtends S (R i) := by
  have ht : ∀ x y z, (∃ i, N i ∧ R i x y z) → A x ∧ B y ∧ D z := by
    intro x y z ⟨i,hi,h⟩
    exact typed i hi x y z h
  obtain ⟨S,hs,e⟩ := countableCondition_representative N A B D rc
    (fun x y z => ∃ i, N i ∧ R i x y z) ht
    (countableDomain_indexed_union_of_wellOrdered_codes N L hw Q hq R W K hk available)
    (ternaryFunctional_directed_union N R functional directed)
  exact ⟨S,hs,fun i hi x y z h => (e x y z).mp ⟨i,hi,h⟩⟩

#classicism_check ternaryFunctional_directed_union countableCondition_directed_lowerBound
#classicism_types ternaryFunctional_directed_union countableCondition_directed_lowerBound
end Classicism.MathematicalContingency
