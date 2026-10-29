import Classicism.Results.MathematicalContingency.FiniteFibreUnions
namespace Classicism.MathematicalContingency
variable {σ α β γ : Type} [Ty σ] [Ty α] [Ty β] [Ty γ]

def TernaryBound (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (n : (σ → Prop) → Prop) (R : α → β → γ → Prop) : Prop :=
  ∀ P : ((σ → Prop) → Prop) → (α → β → γ → Prop) → Prop,
    (∀ R, TernaryEmpty R → P (AtLeastZero σ) R) →
    (∀ n R, LowerNat n → P n R → P (SucCard n) R) →
    (∀ n R S x y z, LowerNat n → A x → B y → D z → TernaryInsert x y z R S → P n R → P (SucCard n) S) → P n R

theorem ternaryBound_zero (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) (he : TernaryEmpty R) : TernaryBound (σ := σ) A B D (AtLeastZero σ) R :=
  fun _ hz _ _ => hz R he

theorem ternaryBound_pad (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (n : (σ → Prop) → Prop) (R : α → β → γ → Prop) (hn : LowerNat n) (h : TernaryBound A B D n R) :
    TernaryBound A B D (SucCard n) R := fun P hz hp hs => hp n R hn (h P hz hp hs)

theorem ternaryBound_insert (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (n : (σ → Prop) → Prop) (R S : α → β → γ → Prop) (x : α) (y : β) (z : γ)
    (hn : LowerNat n) (hx : A x) (hy : B y) (hz : D z) (hi : TernaryInsert x y z R S)
    (h : TernaryBound A B D n R) : TernaryBound A B D (SucCard n) S :=
  fun P h0 hp hs => hs n R S x y z hn hx hy hz hi (h P h0 hp hs)

theorem ternaryBound_data (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (n : (σ → Prop) → Prop) (R : α → β → γ → Prop) (h : TernaryBound A B D n R) :
    LowerNat n ∧ FiniteTernary A B D R :=
  h (fun n R => LowerNat n ∧ FiniteTernary A B D R)
    (fun R he => ⟨lowerNat_zero,finiteTernary_empty A B D R he⟩)
    (fun n _ hn ih => ⟨lowerNat_suc n hn,ih.2⟩)
    (fun n R S x y z hn hx hy hz hi ih => ⟨lowerNat_suc n hn,finiteTernary_insert A B D R S x y z hx hy hz hi ih.2⟩)

theorem finiteTernary_has_bound (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) (hr : FiniteTernary A B D R) :
    ∃ n : (σ → Prop) → Prop, LowerNat n ∧ TernaryBound A B D n R :=
  hr (fun R => ∃ n : (σ → Prop) → Prop, LowerNat n ∧ TernaryBound A B D n R)
    (fun R he => ⟨AtLeastZero σ,lowerNat_zero,ternaryBound_zero A B D R he⟩)
    (fun R S x y z hx hy hz hi ih => ih.elim fun n h =>
      ⟨SucCard n,lowerNat_suc n h.1,ternaryBound_insert A B D n R S x y z h.1 hx hy hz hi h.2⟩)

theorem ternaryBound_induction (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (P : ((σ → Prop) → Prop) → (α → β → γ → Prop) → Prop)
    (hz : ∀ R, TernaryEmpty R → P (AtLeastZero σ) R)
    (hp : ∀ n R, LowerNat n → TernaryBound A B D n R → P n R → P (SucCard n) R)
    (hs : ∀ n R S x y z, LowerNat n → A x → B y → D z → TernaryInsert x y z R S →
      TernaryBound A B D n R → P n R → P (SucCard n) S)
    (n : (σ → Prop) → Prop) (R : α → β → γ → Prop) (h : TernaryBound A B D n R) : P n R :=
  (h (fun n R => TernaryBound A B D n R ∧ P n R)
    (fun R he => ⟨ternaryBound_zero A B D R he,hz R he⟩)
    (fun n R hn ih => ⟨ternaryBound_pad A B D n R hn ih.1,hp n R hn ih.1 ih.2⟩)
    (fun n R S x y z hn hx hy hz hi ih => ⟨ternaryBound_insert A B D n R S x y z hn hx hy hz hi ih.1,
      hs n R S x y z hn hx hy hz hi ih.1 ih.2⟩)).2

theorem ternaryBound_cases (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (n : (σ → Prop) → Prop) (R : α → β → γ → Prop) (h : TernaryBound A B D n R) :
    (n = AtLeastZero σ ∧ TernaryEmpty R) ∨
    ∃ m, LowerNat m ∧ n = SucCard m ∧ (TernaryBound A B D m R ∨
      ∃ S x y z, A x ∧ B y ∧ D z ∧ TernaryInsert x y z S R ∧ TernaryBound A B D m S) :=
  ternaryBound_induction A B D
    (fun n R => (n = AtLeastZero σ ∧ TernaryEmpty R) ∨
      ∃ m, LowerNat m ∧ n = SucCard m ∧ (TernaryBound A B D m R ∨
        ∃ S x y z, A x ∧ B y ∧ D z ∧ TernaryInsert x y z S R ∧ TernaryBound A B D m S))
    (fun R he => Or.inl ⟨rfl,he⟩)
    (fun n R hn hr _ => Or.inr ⟨n,hn,rfl,Or.inl hr⟩)
    (fun n R S x y z hn hx hy hz hi hr _ => Or.inr ⟨n,hn,rfl,Or.inr ⟨R,x,y,z,hx,hy,hz,hi,hr⟩⟩) n R h

theorem ternaryBound_zero_empty (hp : LowerPeano σ) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) (h : TernaryBound A B D (AtLeastZero σ) R) : TernaryEmpty R :=
  (ternaryBound_cases A B D _ R h).elim (fun h => h.2)
    (fun h => h.elim fun n hn => (hp.1 n hn.1 hn.2.1).elim)

#classicism_check ternaryBound_zero ternaryBound_pad ternaryBound_insert ternaryBound_data finiteTernary_has_bound ternaryBound_induction ternaryBound_cases ternaryBound_zero_empty
#classicism_types ternaryBound_zero ternaryBound_pad ternaryBound_insert ternaryBound_data finiteTernary_has_bound ternaryBound_induction ternaryBound_cases ternaryBound_zero_empty
end Classicism.MathematicalContingency
