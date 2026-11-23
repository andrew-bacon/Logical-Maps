import Classicism.Results.MathematicalContingency.NaturalPairing

/-! Current finiteness of ternary graphs, without numerical sequence codes.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

def TernaryEmpty (R : α → β → γ → Prop) : Prop := ∀ x y z, ¬ R x y z

def TernaryInsert (x : α) (y : β) (z : γ) (R S : α → β → γ → Prop) : Prop :=
  ∀ u v w, S u v w ↔ R u v w ∨ (u = x ∧ v = y ∧ w = z)

def FiniteTernary (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) : Prop :=
  ∀ P : (α → β → γ → Prop) → Prop,
    (∀ R, TernaryEmpty R → P R) →
    (∀ R S x y z, A x → B y → D z → TernaryInsert x y z R S → P R → P S) → P R

variable (A : α → Prop) (B : β → Prop) (D : γ → Prop)

theorem finiteTernary_empty (R : α → β → γ → Prop) (h : TernaryEmpty R) :
    FiniteTernary A B D R := fun _ hz _ => hz R h

theorem finiteTernary_insert (R S : α → β → γ → Prop) (x : α) (y : β) (z : γ)
    (hx : A x) (hy : B y) (hz : D z) (hi : TernaryInsert x y z R S)
    (h : FiniteTernary A B D R) : FiniteTernary A B D S :=
  fun P h0 hs => hs R S x y z hx hy hz hi (h P h0 hs)

theorem finiteTernary_induction (P : (α → β → γ → Prop) → Prop)
    (h0 : ∀ R, TernaryEmpty R → P R)
    (step : ∀ R S x y z, A x → B y → D z → TernaryInsert x y z R S →
      FiniteTernary A B D R → P R → P S)
    (R : α → β → γ → Prop) (h : FiniteTernary A B D R) : P R :=
  (h (fun R => FiniteTernary A B D R ∧ P R)
    (fun R he => ⟨finiteTernary_empty A B D R he,h0 R he⟩)
    (fun R S x y z hx hy hz hi ih =>
      ⟨finiteTernary_insert A B D R S x y z hx hy hz hi ih.1,step R S x y z hx hy hz hi ih.1 ih.2⟩)).2

theorem finiteTernary_members (R : α → β → γ → Prop) (h : FiniteTernary A B D R) :
    ∀ x y z, R x y z → A x ∧ B y ∧ D z := by
  apply h (fun R => ∀ x y z, R x y z → A x ∧ B y ∧ D z) ?_ ?_
  · intro R he x y z hr
    exact (he x y z hr).elim
  · intro R S x y z hx hy hz hi ih u v w hs
    obtain hr | ⟨eu,ev,ew⟩ := (hi u v w).mp hs
    · exact ih u v w hr
    · exact ⟨eu.symm ▸ hx,ev.symm ▸ hy,ew.symm ▸ hz⟩

theorem finiteTernary_cases (R : α → β → γ → Prop) (h : FiniteTernary A B D R) :
    TernaryEmpty R ∨ ∃ S x y z, A x ∧ B y ∧ D z ∧ FiniteTernary A B D S ∧ TernaryInsert x y z S R :=
  finiteTernary_induction A B D
    (fun R => TernaryEmpty R ∨ ∃ S x y z, A x ∧ B y ∧ D z ∧ FiniteTernary A B D S ∧ TernaryInsert x y z S R)
    (fun R he => Or.inl he)
    (fun R S x y z hx hy hz hi hf _ => Or.inr ⟨R,x,y,z,hx,hy,hz,hf,hi⟩) R h

theorem finiteTernary_coext (R S : α → β → γ → Prop) (h : FiniteTernary A B D R)
    (e : ∀ x y z, R x y z ↔ S x y z) : FiniteTernary A B D S := by
  obtain he | ⟨H,x,y,z,hx,hy,hz,hf,hi⟩ := finiteTernary_cases A B D R h
  · exact finiteTernary_empty A B D S (fun x y z hs => he x y z ((e x y z).mpr hs))
  · exact finiteTernary_insert A B D H S x y z hx hy hz
      (fun u v w => (e u v w).symm.trans (hi u v w)) hf

theorem finiteTernary_singleton (x : α) (y : β) (z : γ) (hx : A x) (hy : B y) (hz : D z) :
    FiniteTernary A B D (fun u v w => u = x ∧ v = y ∧ w = z) := by
  apply finiteTernary_insert A B D (fun _ _ _ => False) _ x y z hx hy hz ?_
    (finiteTernary_empty A B D _ (fun _ _ _ h => h))
  intro u v w
  exact ⟨Or.inr,fun h => h.elim False.elim id⟩

theorem finiteTernary_union (R S : α → β → γ → Prop)
    (hr : FiniteTernary A B D R) (hs : FiniteTernary A B D S) :
    FiniteTernary A B D (fun x y z => R x y z ∨ S x y z) := by
  apply hr (fun R => FiniteTernary A B D (fun x y z => R x y z ∨ S x y z)) ?_ ?_
  · intro R he
    exact finiteTernary_coext A B D S _ hs (fun x y z =>
      ⟨Or.inr,fun h => h.elim (fun h => (he x y z h).elim) id⟩)
  · intro R T x y z hx hy hz hi ih
    apply finiteTernary_insert A B D (fun u v w => R u v w ∨ S u v w) _ x y z hx hy hz ?_ ih
    intro u v w
    constructor
    · intro h
      obtain ht | hs := h
      · exact ((hi u v w).mp ht).elim (fun hr => Or.inl (Or.inl hr)) Or.inr
      · exact Or.inl (Or.inr hs)
    · intro h
      obtain h | he := h
      · exact h.elim (fun hr => Or.inl ((hi u v w).mpr (Or.inl hr))) Or.inr
      · exact Or.inl ((hi u v w).mpr (Or.inr he))

theorem finiteTernary_subset (R S : α → β → γ → Prop)
    (hr : FiniteTernary A B D R) (hsub : ∀ x y z, S x y z → R x y z) :
    FiniteTernary A B D S := by
  have main : ∀ (R : α → β → γ → Prop), FiniteTernary A B D R →
      ∀ S, (∀ x y z, S x y z → R x y z) → FiniteTernary A B D S := by
    intro R hr
    apply hr (fun R => ∀ S, (∀ x y z, S x y z → R x y z) → FiniteTernary A B D S) ?_ ?_
    · intro R he S hsub
      exact finiteTernary_empty A B D S (fun x y z hs => he x y z (hsub x y z hs))
    · intro R T x y z hx hy hz hi ih S hsub
      obtain hp | hp := em (S x y z)
      · have hf := ih (fun u v w => S u v w ∧ R u v w) (fun _ _ _ h => h.2)
        apply finiteTernary_insert A B D (fun u v w => S u v w ∧ R u v w) S x y z hx hy hz ?_ hf
        intro u v w
        constructor
        · intro hs
          exact ((hi u v w).mp (hsub u v w hs)).elim (fun hr => Or.inl ⟨hs,hr⟩) Or.inr
        · intro h
          obtain h | ⟨eu,ev,ew⟩ := h
          · exact h.1
          · subst u; subst v; subst w
            exact hp
      · apply ih S
        intro u v w hs
        obtain hr | ⟨eu,ev,ew⟩ := (hi u v w).mp (hsub u v w hs)
        · exact hr
        · subst u; subst v; subst w
          exact (hp hs).elim
  exact main R hr S hsub

theorem finiteTernary_restrict (R : α → β → γ → Prop) (Q : α → β → γ → Prop)
    (hr : FiniteTernary A B D R) : FiniteTernary A B D (fun x y z => R x y z ∧ Q x y z) :=
  finiteTernary_subset A B D R _ hr (fun _ _ _ h => h.1)

variable {σ : Type} [Ty σ]

theorem finiteTernary_nat_bound (hp : LowerPeano σ) (B : β → Prop) (D : γ → Prop)
    (R : ((σ → Prop) → Prop) → β → γ → Prop) (h : FiniteTernary LowerNat B D R) :
    ∃ k, LowerNat k ∧ ∀ n a b, R n a b → LowerLT n k := by
  apply h (fun R => ∃ k, LowerNat k ∧ ∀ n a b, R n a b → LowerLT n k) ?_ ?_
  · intro R he
    exact ⟨AtLeastZero σ,lowerNat_zero,fun n a b hr => (he n a b hr).elim⟩
  · intro R S n a b hn ha hb hi ih
    obtain ⟨k,hk,hbound⟩ := ih
    obtain hnk | hkn := lowerLE_total n k hn hk
    · refine ⟨SucCard k,lowerNat_suc k hk,?_⟩
      intro m x y hs
      obtain hr | ⟨em,ex,ey⟩ := (hi m x y).mp hs
      · exact lowerLT_of_lt_of_le hp m k (SucCard k) (hbound m x y hr) (lowerLT_suc hp k hk).1
      · subst m
        exact lowerLT_of_le_of_lt hp n k (SucCard k) hnk (lowerLT_suc hp k hk)
    · refine ⟨SucCard n,lowerNat_suc n hn,?_⟩
      intro m x y hs
      obtain hr | ⟨em,ex,ey⟩ := (hi m x y).mp hs
      · exact lowerLT_of_lt_of_le hp m k (SucCard n) (hbound m x y hr)
          (lowerLE_trans k n (SucCard n) hkn (lowerLT_suc hp n hn).1)
      · subst m
        exact lowerLT_suc hp n hn

theorem finiteTernary_fresh_nat (hp : LowerPeano σ) (B : β → Prop) (D : γ → Prop)
    (R : ((σ → Prop) → Prop) → β → γ → Prop) (h : FiniteTernary LowerNat B D R) :
    ∃ k, LowerNat k ∧ ∀ a b, ¬ R k a b := by
  obtain ⟨k,hk,hbound⟩ := finiteTernary_nat_bound hp B D R h
  exact ⟨k,hk,fun a b hr => lowerLT_irrefl k (hbound k a b hr)⟩

#classicism_check finiteTernary_empty finiteTernary_insert finiteTernary_induction
  finiteTernary_members finiteTernary_cases finiteTernary_coext finiteTernary_singleton
  finiteTernary_union finiteTernary_subset finiteTernary_restrict finiteTernary_nat_bound
  finiteTernary_fresh_nat
#classicism_types finiteTernary_empty finiteTernary_insert finiteTernary_induction
  finiteTernary_members finiteTernary_cases finiteTernary_coext finiteTernary_singleton
  finiteTernary_union finiteTernary_subset finiteTernary_restrict finiteTernary_nat_bound
  finiteTernary_fresh_nat
end Classicism.MathematicalContingency
