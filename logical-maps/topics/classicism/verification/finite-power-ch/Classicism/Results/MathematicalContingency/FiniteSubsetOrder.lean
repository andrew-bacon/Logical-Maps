import Classicism.Results.MathematicalContingency.FiniteSubsets

/-! Finite subsets in a current linear order.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

theorem finiteSubset_empty_or_greatest (A : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (X : α → Prop) (hf : FiniteSubset A X) :
    (∀ x, ¬ X x) ∨ ∃ a, X a ∧ ∀ x, X x → x = a ∨ L x a := by
  exact finiteSubset_induction A
    (fun X => (∀ x, ¬ X x) ∨ ∃ a, X a ∧ ∀ x, X x → x = a ∨ L x a)
    (fun _ he => Or.inl he) (by
      intro X Y a ha hi hX ih
      have hya : Y a := (hi a).mpr (Or.inr rfl)
      obtain he | ⟨b,hb,hm⟩ := ih
      · exact Or.inr ⟨a,hya,fun x hx => ((hi x).mp hx).elim
          (fun hx => (he x hx).elim) Or.inl⟩
      · have hba := finiteSubset_members A X hX b hb
        obtain e | hab | hbaL := hl.2.2.2 a b ha hba
        · subst b
          exact Or.inr ⟨a,hya,fun x hx => ((hi x).mp hx).elim (hm x) Or.inl⟩
        · exact Or.inr ⟨b,(hi b).mpr (Or.inl hb),fun x hx => ((hi x).mp hx).elim
            (hm x) (fun e => Or.inr (e ▸ hab))⟩
        · refine Or.inr ⟨a,hya,?_⟩
          intro x hx
          obtain hx | e := (hi x).mp hx
          · exact (hm x hx).elim (fun e => Or.inr (e ▸ hbaL))
              (fun hxb => Or.inr (hl.2.2.1 x b a (finiteSubset_members A X hX x hx) hba ha hxb hbaL))
          · exact Or.inl e) X hf

theorem finiteSubset_greatest (A : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (X : α → Prop) (hf : FiniteSubset A X) (he : ∃ x, X x) :
    ∃ a, X a ∧ ∀ x, X x → x = a ∨ L x a :=
  (finiteSubset_empty_or_greatest A L hl X hf).elim
    (fun hn => he.elim (fun x hx => (hn x hx).elim)) id

theorem finiteSubset_strict_bound (A : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (inhabited : ∃ a, A a)
    (noLast : ∀ a, A a → ∃ b, A b ∧ L a b)
    (X : α → Prop) (hf : FiniteSubset A X) : ∃ b, A b ∧ ∀ x, X x → L x b := by
  obtain he | ⟨a,ha,hm⟩ := finiteSubset_empty_or_greatest A L hl X hf
  · obtain ⟨b,hb⟩ := inhabited
    exact ⟨b,hb,fun x hx => (he x hx).elim⟩
  · have haa := finiteSubset_members A X hf a ha
    obtain ⟨b,hb,hab⟩ := noLast a haa
    exact ⟨b,hb,fun x hx => (hm x hx).elim (fun e => e ▸ hab)
      (fun hxa => hl.2.2.1 x a b (finiteSubset_members A X hf x hx) haa hb hxa hab)⟩

#classicism_check finiteSubset_empty_or_greatest finiteSubset_greatest finiteSubset_strict_bound
#classicism_types finiteSubset_empty_or_greatest finiteSubset_greatest finiteSubset_strict_bound
end Classicism.MathematicalContingency
