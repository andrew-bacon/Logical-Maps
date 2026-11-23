import Classicism.Results.MathematicalContingency.NaturalWellOrder
import Classicism.Results.MathematicalContingency.CountableConditionUnions
import Classicism.Results.MathematicalContingency.SerialCounting

/-! A countable domain uses countably many rows. Least domain codes select
one code per used row, so no countable choice is needed to find a fresh row. -/
namespace Classicism.MathematicalContingency
variable {ν α β γ : Type} [Ty ν] [Ty α] [Ty β] [Ty γ]

theorem countableDomain_rows_embed (N : ν → Prop) (L : ν → ν → Prop)
    (hw : WellOrderOn N L) (R : α → β → γ → Prop) (hr : CountableDomain N R) :
    Embeds (fun y => ∃ x z, R x y z) N := by
  obtain ⟨F,hf,ft,_,fi⟩ := hr
  let B : β → Prop := fun y => ∃ x z, R x y z
  let J : β → ν → Prop := fun y n => ∃ x, F x y n
  have serial : ∀ y, B y → ∃ n, N n ∧ J y n := by
    intro y hy
    obtain ⟨x,z,hz⟩ := hy
    obtain ⟨n,hn⟩ := ft x y z hz
    exact ⟨n,(hf x y n hn).1,x,hn⟩
  refine ⟨LeastRelated B N L J,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro y n h
    exact ⟨h.1,h.2.1⟩
  · intro y hy
    obtain ⟨n,hn⟩ := leastRelated_exists B N L J hw serial y hy
    exact ⟨n,hn.2.1,hn⟩
  · intro y n m hn hm
    exact leastRelated_unique B N L J hw y n m hn hm
  · intro y v n hy hv
    obtain ⟨x,hx⟩ := hy.2.2.1
    obtain ⟨u,hu⟩ := hv.2.2.1
    exact (fi x y u v n hx hu).2

theorem countableDomain_unused_row (N : ν → Prop) (L : ν → ν → Prop)
    (hw : WellOrderOn N L) (B : β → Prop) (large : ¬ Embeds B N)
    (R : α → β → γ → Prop) (hr : CountableDomain N R) :
    ∃ a, B a ∧ ∀ x z, ¬ R x a z := by
  obtain h | h := em (∃ a, B a ∧ ∀ x z, ¬ R x a z)
  · exact h
  · have sub : ∀ a, B a → ∃ x z, R x a z := by
      intro a ha
      obtain he | he := em (∃ x z, R x a z)
      · exact he
      · exact (h ⟨a,ha,fun x z hz => he ⟨x,z,hz⟩⟩).elim
    exact (large (embeds_trans B (fun a => ∃ x z, R x a z) N
      (embeds_of_subset B _ sub) (countableDomain_rows_embed N L hw R hr))).elim

variable {σ : Type} [Ty σ]
theorem natural_countableCondition_covers_row (hp : LowerPeano σ)
    (B : β → Prop) (D : γ → Prop) (large : ¬ Embeds B (@LowerNat σ _))
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → β → γ → Prop))
    (R : ((σ → Prop) → Prop) → β → γ → Prop)
    (hr : CountableCondition (@LowerNat σ _) LowerNat B D R)
    (F : ((σ → Prop) → Prop) → γ → Prop) (hf : Maps F LowerNat D) :
    ∃ T a, CountableCondition (@LowerNat σ _) LowerNat B D T ∧ B a ∧
      TernaryExtends T R ∧ ∀ x z, F x z → T x a z := by
  obtain ⟨a,ha,fresh⟩ := countableDomain_unused_row LowerNat LowerLT
    (lowerNat_wellOrder hp) B large R hr.2.2.1
  obtain ⟨T,ht,ext,row⟩ := natural_countableCondition_add_row hp B D rc R hr F hf a ha fresh
  exact ⟨T,a,ht,ha,ext,row⟩

#classicism_check countableDomain_rows_embed countableDomain_unused_row natural_countableCondition_covers_row
#classicism_types countableDomain_rows_embed countableDomain_unused_row natural_countableCondition_covers_row
end Classicism.MathematicalContingency
