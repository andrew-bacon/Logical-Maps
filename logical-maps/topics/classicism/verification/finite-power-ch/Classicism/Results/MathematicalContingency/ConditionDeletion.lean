import Classicism.Results.MathematicalContingency.TernaryDeletion
namespace Classicism.MathematicalContingency
variable {σ α β γ : Type} [Ty σ] [Ty α] [Ty β] [Ty γ]

def ReducedAt (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (x : α) (y : β) (z : γ) (R S : α → β → γ → Prop) : Prop :=
  FiniteCondition A B D S ∧ ∀ u v w, S u v w ↔ TernaryErase x y z R u v w

def IncompatibleFamily (U : (α → β → γ → Prop) → Prop) : Prop :=
  ∀ R S, U R → U S → R ≠ S → ¬ TernaryAgree R S

theorem reducedAt_exists (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (α → β → γ → Prop)) (x : α) (y : β) (z : γ)
    (R : α → β → γ → Prop) (hr : FiniteCondition A B D R) : ∃ S, ReducedAt A B D x y z R S := by
  obtain ⟨S,hs,he⟩ := finiteCondition_representative A B D rc (TernaryErase x y z R)
    (finiteTernary_subset A B D R _ hr.2.1 (fun _ _ _ h => h.1))
    (ternaryFunctional_subset R _ hr.2.2 (fun _ _ _ h => h.1))
  exact ⟨S,hs,fun u v w => (he u v w).symm⟩

theorem reducedAt_unique (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (x : α) (y : β) (z : γ) (R S T : α → β → γ → Prop)
    (hs : ReducedAt A B D x y z R S) (ht : ReducedAt A B D x y z R T) : S = T :=
  rigid_eq_of_coext S T hs.1.1 ht.1.1 (fun u v w => (hs.2 u v w).trans (ht.2 u v w).symm)

theorem reducedAt_injective (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (x : α) (y : β) (z : γ) (R S T : α → β → γ → Prop)
    (hr : FiniteCondition A B D R) (hs : FiniteCondition A B D S) (hR : R x y z) (hS : S x y z)
    (hRT : ReducedAt A B D x y z R T) (hST : ReducedAt A B D x y z S T) : R = S := by
  apply rigid_eq_of_coext R S hr.1 hs.1
  intro u v w
  have h := (ternaryErase_restore R x y z hR) u v w
  have k := (ternaryErase_restore S x y z hS) u v w
  constructor
  · intro hv
    exact k.mpr ((h.mp hv).elim
      (fun h => Or.inl ((hST.2 u v w).mp ((hRT.2 u v w).mpr h))) Or.inr)
  · intro hv
    exact h.mpr ((k.mp hv).elim
      (fun h => Or.inl ((hRT.2 u v w).mp ((hST.2 u v w).mpr h))) Or.inr)

theorem reducedAt_bound (hp : LowerPeano σ) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (x : α) (y : β) (z : γ) (n : (σ → Prop) → Prop) (R S : α → β → γ → Prop)
    (hn : LowerNat n) (hb : TernaryBound A B D (SucCard n) R) (hit : R x y z)
    (hs : ReducedAt A B D x y z R S) : TernaryBound A B D n S :=
  ternaryBound_subset A B D n _ S (ternaryBound_erase hp A B D n R hn hb x y z hit)
    (fun u v w h => (hs.2 u v w).mp h)

theorem reducedAt_agree (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (x : α) (y : β) (z : γ) (R S V W : α → β → γ → Prop)
    (hr : FiniteCondition A B D R) (hs : FiniteCondition A B D S) (hR : R x y z) (hS : S x y z)
    (hRV : ReducedAt A B D x y z R V) (hSW : ReducedAt A B D x y z S W)
    (ha : TernaryAgree V W) : TernaryAgree R S := by
  intro u v p q hRp hSq
  obtain ep | enp := em (u = x ∧ v = y ∧ p = z)
  · have hSp : S u v p := ep.1.symm ▸ ep.2.1.symm ▸ ep.2.2.symm ▸ hS
    exact hs.2.2 u v p q hSp hSq
  · obtain eq | enq := em (u = x ∧ v = y ∧ q = z)
    · have hRq : R u v q := eq.1.symm ▸ eq.2.1.symm ▸ eq.2.2.symm ▸ hR
      exact hr.2.2 u v p q hRp hRq
    · exact ha u v p q ((hRV.2 u v p).mpr ⟨hRp,enp⟩) ((hSW.2 u v q).mpr ⟨hSq,enq⟩)

theorem reducedAt_image_incompatible (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (x : α) (y : β) (z : γ) (U : (α → β → γ → Prop) → Prop)
    (sub : ∀ R, U R → FiniteCondition A B D R) (hit : ∀ R, U R → R x y z)
    (inc : IncompatibleFamily U) :
    IncompatibleFamily (fun S => ∃ R, U R ∧ ReducedAt A B D x y z R S) := by
  intro V W hV hW hne hagr
  obtain ⟨R,hR,hRV⟩ := hV
  obtain ⟨S,hS,hSW⟩ := hW
  have hRS : R ≠ S := fun e => hne (reducedAt_unique A B D x y z S V W (e ▸ hRV) hSW)
  exact inc R S hR hS hRS
    (reducedAt_agree A B D x y z R S V W (sub R hR) (sub S hS) (hit R hR) (hit S hS) hRV hSW hagr)

/-- The induction step for a family sharing one fixed assignment. -/
theorem bounded_fixed_assignment_finite (hp : LowerPeano σ)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (α → β → γ → Prop)) (n : (σ → Prop) → Prop) (hn : LowerNat n)
    (ih : ∀ V, (∀ R, V R → FiniteCondition A B D R ∧ TernaryBound A B D n R) →
      IncompatibleFamily V → FiniteSubset (FiniteCondition A B D) V)
    (x : α) (y : β) (z : γ) (U : (α → β → γ → Prop) → Prop)
    (sub : ∀ R, U R → FiniteCondition A B D R ∧ TernaryBound A B D (SucCard n) R)
    (hit : ∀ R, U R → R x y z) (inc : IncompatibleFamily U) : FiniteSubset (FiniteCondition A B D) U := by
  let V := fun S => ∃ R, U R ∧ ReducedAt A B D x y z R S
  have hv : FiniteSubset (FiniteCondition A B D) V := ih V
    (fun S h => h.elim fun R hR => ⟨hR.2.1,reducedAt_bound hp A B D x y z n R S hn (sub R hR.1).2 (hit R hR.1) hR.2⟩)
    (reducedAt_image_incompatible A B D x y z U (fun R h => (sub R h).1) hit inc)
  apply finiteSubset_injective_preimage (FiniteCondition A B D) U (FiniteCondition A B D) V
    (ReducedAt A B D x y z) hv (fun R h => (sub R h).1) ?_ ?_
  · intro R hR
    obtain ⟨S,hS⟩ := reducedAt_exists A B D rc x y z R (sub R hR).1
    exact ⟨S,⟨R,hR,hS⟩,hS⟩
  · intro R S T hR hS hRT hST
    exact reducedAt_injective A B D x y z R S T (sub R hR).1 (sub S hS).1 (hit R hR) (hit S hS) hRT hST

#classicism_check reducedAt_exists reducedAt_unique reducedAt_injective reducedAt_bound reducedAt_agree reducedAt_image_incompatible bounded_fixed_assignment_finite
#classicism_types reducedAt_exists reducedAt_unique reducedAt_injective reducedAt_bound reducedAt_agree reducedAt_image_incompatible bounded_fixed_assignment_finite
end Classicism.MathematicalContingency
