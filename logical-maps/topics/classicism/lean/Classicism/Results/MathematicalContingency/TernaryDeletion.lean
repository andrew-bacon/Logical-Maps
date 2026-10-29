import Classicism.Results.MathematicalContingency.TernarySizeBound
namespace Classicism.MathematicalContingency
variable {σ α β γ : Type} [Ty σ] [Ty α] [Ty β] [Ty γ]

def TernaryErase (x : α) (y : β) (z : γ) (R : α → β → γ → Prop) : α → β → γ → Prop :=
  fun u v w => R u v w ∧ ¬ (u = x ∧ v = y ∧ w = z)

theorem ternaryBound_subset (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (n : (σ → Prop) → Prop) (R S : α → β → γ → Prop) (hr : TernaryBound A B D n R)
    (sub : ∀ x y z, S x y z → R x y z) : TernaryBound A B D n S := by
  have h := hr (fun (n : (σ → Prop) → Prop) (R : α → β → γ → Prop) => ∀ S : α → β → γ → Prop, (∀ x y z, S x y z → R x y z) → TernaryBound A B D n S)
    (fun R he S hs => ternaryBound_zero A B D S (fun x y z h => he x y z (hs x y z h)))
    (fun n R hn ih S hs => ternaryBound_pad A B D n S hn (ih S hs))
    (by
      intro n R T x y z hn hx hy hz hi ih S sub
      obtain hS | hS := em (S x y z)
      · have hf := ih (fun u v w => S u v w ∧ R u v w) (fun _ _ _ h => h.2)
        apply ternaryBound_insert A B D n _ S x y z hn hx hy hz ?_ hf
        intro u v w
        constructor
        · intro hs
          exact ((hi u v w).mp (sub u v w hs)).elim (fun h => Or.inl ⟨hs,h⟩) Or.inr
        · intro h
          obtain h | ⟨eu,ev,ew⟩ := h
          · exact h.1
          · exact eu.symm ▸ ev.symm ▸ ew.symm ▸ hS
      · apply ternaryBound_pad A B D n S hn (ih S ?_)
        intro u v w hs
        obtain h | ⟨eu,ev,ew⟩ := (hi u v w).mp (sub u v w hs)
        · exact h
        · exact (hS (eu ▸ ev ▸ ew ▸ hs)).elim)
  exact h S sub

theorem ternaryErase_restore (R : α → β → γ → Prop) (x : α) (y : β) (z : γ) (h : R x y z) :
    TernaryInsert x y z (TernaryErase x y z R) R := by
  intro u v w
  constructor
  · intro hr
    exact (em (u = x ∧ v = y ∧ w = z)).elim Or.inr (fun hn => Or.inl ⟨hr,hn⟩)
  · intro hr
    exact hr.elim (fun h => h.1) (fun e => e.1.symm ▸ e.2.1.symm ▸ e.2.2.symm ▸ h)

theorem ternaryErase_insert_other (R S : α → β → γ → Prop)
    (x a : α) (y b : β) (z c : γ) (hi : TernaryInsert a b c R S)
    (hn : ¬ (a = x ∧ b = y ∧ c = z)) :
    TernaryInsert a b c (TernaryErase x y z R) (TernaryErase x y z S) := by
  intro u v w
  constructor
  · intro h
    exact ((hi u v w).mp h.1).elim (fun hr => Or.inl ⟨hr,h.2⟩) Or.inr
  · intro h
    obtain h | ⟨ea,eb,ec⟩ := h
    · exact ⟨(hi u v w).mpr (Or.inl h.1),h.2⟩
    · exact ⟨(hi u v w).mpr (Or.inr ⟨ea,eb,ec⟩),fun e => hn ⟨ea.symm.trans e.1,eb.symm.trans e.2.1,ec.symm.trans e.2.2⟩⟩

theorem ternaryErase_insert_same_subset (R S : α → β → γ → Prop)
    (x : α) (y : β) (z : γ) (hi : TernaryInsert x y z R S) :
    ∀ u v w, TernaryErase x y z S u v w → R u v w :=
  fun u v w h => ((hi u v w).mp h.1).elim id (fun e => (h.2 e).elim)

/-- Removing a present assignment lowers an at-most bound by one. -/
theorem ternaryBound_erase (hp : LowerPeano σ) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (m : (σ → Prop) → Prop) (R : α → β → γ → Prop) (hm : LowerNat m)
    (hr : TernaryBound A B D (SucCard m) R) (x : α) (y : β) (z : γ) (hit : R x y z) :
    TernaryBound A B D m (TernaryErase x y z R) := by
  have main := ternaryBound_induction A B D
    (fun n R => ∀ m, LowerNat m → n = SucCard m → R x y z → TernaryBound A B D m (TernaryErase x y z R))
    (fun R he _ _ _ h => (he x y z h).elim)
    (by
      intro n R hn hr _ m hm e _
      have en := hp.2 n m hn hm e
      exact en ▸ ternaryBound_subset A B D n R _ hr (fun _ _ _ h => h.1))
    (by
      intro n R S a b c hn ha hb hc hi hr ih m hm e hit
      have en := hp.2 n m hn hm e
      have target : TernaryBound A B D n (TernaryErase x y z S) := by
        obtain heq | hne := em (a = x ∧ b = y ∧ c = z)
        · have ins : TernaryInsert x y z R S := heq.1 ▸ heq.2.1 ▸ heq.2.2 ▸ hi
          exact ternaryBound_subset A B D n R _ hr (ternaryErase_insert_same_subset R S x y z ins)
        · have hR : R x y z := ((hi x y z).mp hit).elim id
            (fun e => (hne ⟨e.1.symm,e.2.1.symm,e.2.2.symm⟩).elim)
          obtain ez | ⟨k,hk,ek⟩ := lowerNat_cases n hn
          · exact (ternaryBound_zero_empty hp A B D R (ez ▸ hr) x y z hR).elim
          · have hdel := ih k hk ek hR
            have hi' := ternaryErase_insert_other R S x a y b z c hi hne
            exact ek.symm ▸ ternaryBound_insert A B D k _ _ a b c hk ha hb hc hi' hdel
      exact en ▸ target) (SucCard m) R hr
  exact main m hm rfl hit

#classicism_check ternaryBound_subset ternaryErase_restore ternaryErase_insert_other ternaryErase_insert_same_subset ternaryBound_erase
#classicism_types ternaryBound_subset ternaryErase_restore ternaryErase_insert_other ternaryErase_insert_same_subset ternaryBound_erase
end Classicism.MathematicalContingency
