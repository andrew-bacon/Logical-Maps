import Classicism.Results.MathematicalContingency.CountableRows

/-! Countable unions with uniform relational domain codes. Least-stage coding
handles repeated coordinates; least-code selection makes the needed uniformity
explicit instead of using a hidden countable-choice principle. -/
namespace Classicism.MathematicalContingency
variable {ν α β γ : Type} [Ty ν] [Ty α] [Ty β] [Ty γ]

def CountableDomainCode (N : ν → Prop) (R : α → β → γ → Prop)
    (F : α → β → ν → Prop) : Prop :=
  (∀ x y n, F x y n → N n ∧ ∃ z, R x y z) ∧
  (∀ x y z, R x y z → ∃ n, F x y n) ∧
  (∀ x y n m, F x y n → F x y m → n = m) ∧
  (∀ x y u v n, F x y n → F u v n → x = u ∧ y = v)

def FirstDomainStage (N : ν → Prop) (L : ν → ν → Prop)
    (R : ν → α → β → γ → Prop) (x : α) (y : β) (i : ν) : Prop :=
  N i ∧ (∃ z, R i x y z) ∧ ∀ j, N j → (∃ z, R j x y z) → ¬ L j i

theorem countableDomainCode_coext (N : ν → Prop) (R : α → β → γ → Prop)
    (F G : α → β → ν → Prop) (hf : CountableDomainCode N R F)
    (e : ∀ x y n, F x y n ↔ G x y n) : CountableDomainCode N R G := by
  refine ⟨fun x y n h => hf.1 x y n ((e x y n).mpr h),?_,?_,?_⟩
  · intro x y z h
    obtain ⟨n,hn⟩ := hf.2.1 x y z h
    exact ⟨n,(e x y n).mp hn⟩
  · intro x y n m hn hm
    exact hf.2.2.1 x y n m ((e x y n).mpr hn) ((e x y m).mpr hm)
  · intro x y u v n hx hu
    exact hf.2.2.2 x y u v n ((e x y n).mpr hx) ((e u v n).mpr hu)

theorem firstDomainStage_exists (N : ν → Prop) (L : ν → ν → Prop)
    (hw : WellOrderOn N L) (R : ν → α → β → γ → Prop) (x : α) (y : β)
    (h : ∃ i, N i ∧ ∃ z, R i x y z) : ∃ i, FirstDomainStage N L R x y i := by
  obtain ⟨i,hi,hm⟩ := hw.2 (fun i => N i ∧ ∃ z, R i x y z) (fun _ h => h.1) h
  exact ⟨i,hi.1,hi.2,fun j hj hz => hm j ⟨hj,hz⟩⟩

theorem firstDomainStage_unique (N : ν → Prop) (L : ν → ν → Prop)
    (hw : WellOrderOn N L) (R : ν → α → β → γ → Prop) (x : α) (y : β)
    (i j : ν) (hi : FirstDomainStage N L R x y i) (hj : FirstDomainStage N L R x y j) : i = j := by
  obtain e | h | h := hw.1.2.2.2 i j hi.1 hj.1
  · exact e
  · exact (hj.2.2 i hi.1 hi.2.1 h).elim
  · exact (hi.2.2 j hj.1 hj.2.1 h).elim

theorem countableDomain_indexed_union (N : ν → Prop) (L : ν → ν → Prop)
    (hw : WellOrderOn N L) (Q : ν → ν → ν → Prop) (hq : PairingOn N Q)
    (R : ν → α → β → γ → Prop) (C : ν → α → β → ν → Prop)
    (codes : ∀ i, N i → CountableDomainCode N (R i) (C i)) :
    CountableDomain N (fun x y z => ∃ i, N i ∧ R i x y z) := by
  let F : α → β → ν → Prop := fun x y k =>
    ∃ i n, FirstDomainStage N L R x y i ∧ C i x y n ∧ Q i n k
  refine ⟨F,?_,?_,?_,?_⟩
  · intro x y k h
    obtain ⟨i,n,hi,hc,hqk⟩ := h
    obtain ⟨_,z,hz⟩ := (codes i hi.1).1 x y n hc
    exact ⟨(hq.1 i n k hqk).2.2,z,i,hi.1,hz⟩
  · intro x y z h
    obtain ⟨i,hi,hz⟩ := h
    obtain ⟨j,hj⟩ := firstDomainStage_exists N L hw R x y ⟨i,hi,z,hz⟩
    obtain ⟨w,hw⟩ := hj.2.1
    obtain ⟨n,hn⟩ := (codes j hj.1).2.1 x y w hw
    obtain ⟨k,_,hk⟩ := hq.2.1 j n hj.1 ((codes j hj.1).1 x y n hn).1
    exact ⟨k,j,n,hj,hn,hk⟩
  · intro x y k l hk hl
    obtain ⟨i,n,hi,hn,hk⟩ := hk
    obtain ⟨j,m,hj,hm,hl⟩ := hl
    have e := firstDomainStage_unique N L hw R x y i j hi hj
    subst j
    have e := (codes i hi.1).2.2.1 x y n m hn hm
    subst m
    exact hq.2.2.1 i n k l hk hl
  · intro x y a b k hx ha
    obtain ⟨i,n,hi,hn,hk⟩ := hx
    obtain ⟨j,m,hj,hm,hl⟩ := ha
    obtain ⟨e,f⟩ := hq.2.2.2 i n j m k hk hl
    subst j
    subst m
    exact (codes i hi.1).2.2.2 x y a b n hn hm

theorem uniformDomainCodes_of_wellOrder (N : ν → Prop)
    (R : ν → α → β → γ → Prop) (W : (α → β → ν → Prop) → Prop)
    (K : (α → β → ν → Prop) → (α → β → ν → Prop) → Prop)
    (hw : WellOrderOn W K)
    (available : ∀ i, N i → ∃ F, W F ∧ CountableDomainCode N (R i) F) :
    ∃ C : ν → α → β → ν → Prop, ∀ i, N i → CountableDomainCode N (R i) (C i) := by
  let J : ν → (α → β → ν → Prop) → Prop := fun i F => CountableDomainCode N (R i) F
  let C : ν → α → β → ν → Prop := fun i x y n => ∃ F, LeastRelated N W K J i F ∧ F x y n
  refine ⟨C,?_⟩
  intro i hi
  obtain ⟨F,hF⟩ := leastRelated_exists N W K J hw available i hi
  apply countableDomainCode_coext N (R i) F (C i) hF.2.2.1
  intro x y n
  constructor
  · intro h
    exact ⟨F,hF,h⟩
  · intro h
    exact h.elim (fun G hg => (leastRelated_unique N W K J hw i G F hg.1 hF) ▸ hg.2)

theorem countableDomain_indexed_union_of_wellOrdered_codes
    (N : ν → Prop) (L : ν → ν → Prop) (hw : WellOrderOn N L)
    (Q : ν → ν → ν → Prop) (hq : PairingOn N Q) (R : ν → α → β → γ → Prop)
    (W : (α → β → ν → Prop) → Prop)
    (K : (α → β → ν → Prop) → (α → β → ν → Prop) → Prop)
    (hk : WellOrderOn W K)
    (available : ∀ i, N i → ∃ F, W F ∧ CountableDomainCode N (R i) F) :
    CountableDomain N (fun x y z => ∃ i, N i ∧ R i x y z) := by
  obtain ⟨C,hC⟩ := uniformDomainCodes_of_wellOrder N R W K hk available
  exact countableDomain_indexed_union N L hw Q hq R C hC

#classicism_check countableDomainCode_coext firstDomainStage_exists firstDomainStage_unique countableDomain_indexed_union uniformDomainCodes_of_wellOrder countableDomain_indexed_union_of_wellOrdered_codes
#classicism_types countableDomainCode_coext firstDomainStage_exists firstDomainStage_unique countableDomain_indexed_union uniformDomainCodes_of_wellOrder countableDomain_indexed_union_of_wellOrdered_codes
end Classicism.MathematicalContingency
