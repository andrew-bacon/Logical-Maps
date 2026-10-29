import Classicism.Results.MathematicalContingency.CountableConditions
import Classicism.Results.MathematicalContingency.PairingAbsorption

/-! Countable unions of two domains use tagged natural codes, preferring the
left code on overlaps. All codes are relations; no choice principle is used. -/
namespace Classicism.MathematicalContingency
variable {ν α β γ : Type} [Ty ν] [Ty α] [Ty β] [Ty γ]

theorem countableDomain_union (N : ν → Prop) (Q : ν → ν → ν → Prop)
    (hq : PairingOn N Q) (u v : ν) (hu : N u) (hv : N v) (hne : u ≠ v)
    (R S : α → β → γ → Prop) (hr : CountableDomain N R) (hs : CountableDomain N S) :
    CountableDomain N (fun x y z => R x y z ∨ S x y z) := by
  obtain ⟨F,hf,ft,fu,fi⟩ := hr
  obtain ⟨G,hg,gt,gu,gi⟩ := hs
  let T : α → β → ν → Prop := fun x y k =>
    (∃ n, F x y n ∧ Q u n k) ∨ ((∀ z, ¬ R x y z) ∧ ∃ n, G x y n ∧ Q v n k)
  refine ⟨T,?_,?_,?_,?_⟩
  · intro x y k h
    obtain ⟨n,hn,hk⟩ | ⟨_,n,hn,hk⟩ := h
    · obtain ⟨_,z,hz⟩ := hf x y n hn
      exact ⟨(hq.1 u n k hk).2.2,z,Or.inl hz⟩
    · obtain ⟨_,z,hz⟩ := hg x y n hn
      exact ⟨(hq.1 v n k hk).2.2,z,Or.inr hz⟩
  · intro x y z h
    obtain ⟨w,hw⟩ | he := em (∃ w, R x y w)
    · obtain ⟨n,hn⟩ := ft x y w hw
      obtain ⟨k,_,hk⟩ := hq.2.1 u n hu (hf x y n hn).1
      exact ⟨k,Or.inl ⟨n,hn,hk⟩⟩
    · have hz : S x y z := h.elim (fun h => (he ⟨z,h⟩).elim) (fun h => h)
      obtain ⟨n,hn⟩ := gt x y z hz
      obtain ⟨k,_,hk⟩ := hq.2.1 v n hv (hg x y n hn).1
      exact ⟨k,Or.inr ⟨fun w hw => he ⟨w,hw⟩,n,hn,hk⟩⟩
  · intro x y k l hk hl
    obtain ⟨n,hn,hk⟩ | ⟨he,n,hn,hk⟩ := hk
    · obtain ⟨m,hm,hl⟩ | ⟨he,m,hm,hl⟩ := hl
      · have e := fu x y n m hn hm
        subst m
        exact hq.2.2.1 u n k l hk hl
      · obtain ⟨_,z,hz⟩ := hf x y n hn
        exact (he z hz).elim
    · obtain ⟨m,hm,hl⟩ | ⟨_,m,hm,hl⟩ := hl
      · obtain ⟨_,z,hz⟩ := hf x y m hm
        exact (he z hz).elim
      · have e := gu x y n m hn hm
        subst m
        exact hq.2.2.1 v n k l hk hl
  · intro x y a b k hx ha
    obtain ⟨n,hn,hk⟩ | ⟨_,n,hn,hk⟩ := hx
    · obtain ⟨m,hm,hl⟩ | ⟨_,m,hm,hl⟩ := ha
      · have e := (hq.2.2.2 u n u m k hk hl).2
        subst m
        exact fi x y a b n hn hm
      · exact (hne (hq.2.2.2 u n v m k hk hl).1).elim
    · obtain ⟨m,hm,hl⟩ | ⟨_,m,hm,hl⟩ := ha
      · exact (hne (hq.2.2.2 v n u m k hk hl).1.symm).elim
      · have e := (hq.2.2.2 v n v m k hk hl).2
        subst m
        exact gi x y a b n hn hm

theorem countableCondition_union (N : ν → Prop) (A : α → Prop) (B : β → Prop)
    (D : γ → Prop) (Q : ν → ν → ν → Prop) (hq : PairingOn N Q)
    (u v : ν) (hu : N u) (hv : N v) (hne : u ≠ v)
    (rc : P.RigidComprehension (α → β → γ → Prop))
    (R S : α → β → γ → Prop) (hr : CountableCondition N A B D R)
    (hs : CountableCondition N A B D S) (agree : TernaryAgree R S) :
    ∃ T, CountableCondition N A B D T ∧ ∀ x y z, T x y z ↔ R x y z ∨ S x y z := by
  obtain ⟨T,ht,e⟩ := countableCondition_representative N A B D rc
    (fun x y z => R x y z ∨ S x y z)
    (fun x y z h => h.elim (hr.2.1 x y z) (hs.2.1 x y z))
    (countableDomain_union N Q hq u v hu hv hne R S hr.2.2.1 hs.2.2.1)
    (ternaryFunctional_union R S hr.2.2.2 hs.2.2.2 agree)
  exact ⟨T,ht,fun x y z => (e x y z).symm⟩

theorem countableCondition_add_row (N : α → Prop) (B : β → Prop) (D : γ → Prop)
    (Q : α → α → α → Prop) (hq : PairingOn N Q)
    (u v : α) (hu : N u) (hv : N v) (hne : u ≠ v)
    (rc : P.RigidComprehension (α → β → γ → Prop))
    (R : α → β → γ → Prop) (hr : CountableCondition N N B D R)
    (F : α → γ → Prop) (hf : Maps F N D) (a : β) (ha : B a)
    (fresh : ∀ x z, ¬ R x a z) :
    ∃ T, CountableCondition N N B D T ∧ TernaryExtends T R ∧ ∀ x z, F x z → T x a z := by
  obtain ⟨S,hs,e⟩ := countableCondition_row N B D rc F hf a ha
  have agree : TernaryAgree R S := by
    intro x y z w hz hw
    have ey := ((e x y w).mp hw).1
    subst y
    exact (fresh x z hz).elim
  obtain ⟨T,ht,et⟩ := countableCondition_union N N B D Q hq u v hu hv hne rc R S hr hs agree
  exact ⟨T,ht,fun x y z h => (et x y z).mpr (Or.inl h),
    fun x z h => (et x a z).mpr (Or.inr ((e x a z).mpr ⟨rfl,h⟩))⟩

variable {σ : Type} [Ty σ]
theorem natural_countableCondition_add_row (hp : LowerPeano σ)
    (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → β → γ → Prop))
    (R : ((σ → Prop) → Prop) → β → γ → Prop)
    (hr : CountableCondition (@LowerNat σ _) LowerNat B D R)
    (F : ((σ → Prop) → Prop) → γ → Prop) (hf : Maps F LowerNat D)
    (a : β) (ha : B a) (fresh : ∀ x z, ¬ R x a z) :
    ∃ T, CountableCondition (@LowerNat σ _) LowerNat B D T ∧
      TernaryExtends T R ∧ ∀ x z, F x z → T x a z :=
  countableCondition_add_row LowerNat B D LowerPair (lowerPair_pairing hp)
    (AtLeastZero σ) (SucCard (AtLeastZero σ)) lowerNat_zero (lowerNat_suc _ lowerNat_zero)
    (lowerNat_ne_suc_self hp _ lowerNat_zero) rc R hr F hf a ha fresh

#classicism_check countableDomain_union countableCondition_union countableCondition_add_row natural_countableCondition_add_row
#classicism_types countableDomain_union countableCondition_union countableCondition_add_row natural_countableCondition_add_row
end Classicism.MathematicalContingency
