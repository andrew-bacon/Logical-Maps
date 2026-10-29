import Classicism.Results.MathematicalContingency.FiniteSubsets
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

theorem finiteSubset_indexed_union (A X : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (hx : FiniteSubset A X) (hf : ∀ a, X a → FiniteSubset B (F a)) :
    FiniteSubset B (fun b => ∃ a, X a ∧ F a b) := by
  have h := hx (fun X => (∀ a, X a → FiniteSubset B (F a)) →
      FiniteSubset B (fun b => ∃ a, X a ∧ F a b))
    (fun X he _ => finiteSubset_empty B _ (fun _ h => h.elim fun a ha => he a ha.1))
    (by
      intro X Y a _ hi ih hf
      have hX := ih (fun x hx => hf x ((hi x).mpr (Or.inl hx)))
      have ha := hf a ((hi a).mpr (Or.inr rfl))
      apply finiteSubset_coext B _ _ (finiteSubset_union B _ _ hX ha)
      intro b
      constructor
      · intro h
        obtain ⟨x,hx,hfb⟩ | hab := h
        · exact ⟨x,(hi x).mpr (Or.inl hx),hfb⟩
        · exact ⟨a,(hi a).mpr (Or.inr rfl),hab⟩
      · intro ⟨x,hx,hfb⟩
        exact ((hi x).mp hx).elim (fun h => Or.inl ⟨x,h,hfb⟩) (fun e => Or.inr (e ▸ hfb)))
  exact h hf

theorem finiteSubset_single_fibre (A : α → Prop) (F : α → Prop)
    (sub : ∀ x, F x → A x) (unique : ∀ x y, F x → F y → x = y) : FiniteSubset A F := by
  obtain he | hn := em (∃ x, F x)
  · obtain ⟨x,hx⟩ := he
    exact finiteSubset_subset A (fun y => y = x) F
      (finiteSubset_singleton A x (sub x hx)) (fun y hy => unique y x hy hx)
  · exact finiteSubset_empty A F (fun x hx => hn ⟨x,hx⟩)

theorem finiteSubset_injective_preimage (A X : α → Prop) (B Y : β → Prop)
    (F : α → β → Prop) (hy : FiniteSubset B Y)
    (sub : ∀ x, X x → A x) (total : ∀ x, X x → ∃ y, Y y ∧ F x y)
    (inj : ∀ x x' y, X x → X x' → F x y → F x' y → x = x') : FiniteSubset A X := by
  have h := finiteSubset_indexed_union B Y A (fun y x => X x ∧ F x y) hy
    (fun y _ => finiteSubset_single_fibre A _ (fun x h => sub x h.1)
      (fun x x' h h' => inj x x' y h.1 h'.1 h.2 h'.2))
  exact finiteSubset_coext A _ X h (fun x => ⟨fun h => h.elim fun _ h => h.2.1,
    fun hx => (total x hx).elim fun y hy => ⟨y,hy.1,hx,hy.2⟩⟩)

theorem finiteTernary_indexed_union (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) (V : δ → Prop) (F : α → β → γ → δ → Prop)
    (hr : FiniteTernary A B D R)
    (hf : ∀ x y z, R x y z → FiniteSubset V (F x y z)) :
    FiniteSubset V (fun v => ∃ x y z, R x y z ∧ F x y z v) := by
  have h := hr (fun R => (∀ x y z, R x y z → FiniteSubset V (F x y z)) →
      FiniteSubset V (fun v => ∃ x y z, R x y z ∧ F x y z v))
    (fun R he _ => finiteSubset_empty V _ (fun _ h => h.elim fun x h => h.elim fun y h => h.elim fun z h => he x y z h.1))
    (by
      intro R S x y z _ _ _ hi ih hf
      have hR := ih (fun u v w h => hf u v w ((hi u v w).mpr (Or.inl h)))
      have ht := hf x y z ((hi x y z).mpr (Or.inr ⟨rfl,rfl,rfl⟩))
      apply finiteSubset_coext V _ _ (finiteSubset_union V _ _ hR ht)
      intro v
      constructor
      · intro h
        obtain ⟨a,b,c,hr,hf⟩ | ht := h
        · exact ⟨a,b,c,(hi a b c).mpr (Or.inl hr),hf⟩
        · exact ⟨x,y,z,(hi x y z).mpr (Or.inr ⟨rfl,rfl,rfl⟩),ht⟩
      · intro ⟨a,b,c,hs,hf⟩
        obtain hr | ⟨ea,eb,ec⟩ := (hi a b c).mp hs
        · exact Or.inl ⟨a,b,c,hr,hf⟩
        · exact Or.inr (ea ▸ eb ▸ ec ▸ hf))
  exact h hf

#classicism_check finiteSubset_indexed_union finiteSubset_single_fibre finiteSubset_injective_preimage finiteTernary_indexed_union
#classicism_types finiteSubset_indexed_union finiteSubset_single_fibre finiteSubset_injective_preimage finiteTernary_indexed_union
end Classicism.MathematicalContingency
