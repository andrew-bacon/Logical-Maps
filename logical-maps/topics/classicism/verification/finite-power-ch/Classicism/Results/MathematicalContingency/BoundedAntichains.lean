import Classicism.Results.MathematicalContingency.ConditionDeletion
import Classicism.Results.MathematicalContingency.CohenConditions
namespace Classicism.MathematicalContingency
variable {σ α β γ : Type} [Ty σ] [Ty α] [Ty β] [Ty γ]

theorem ternary_conflict_of_not_agree (R S : α → β → γ → Prop) (h : ¬ TernaryAgree R S) :
    ∃ x y z w, R x y z ∧ S x y w ∧ z ≠ w := by
  apply (em (∃ x y z w, R x y z ∧ S x y w ∧ z ≠ w)).elim id
  intro hn
  apply False.elim (h ?_)
  intro x y z w hr hs
  exact (em (z = w)).elim id (fun he => (hn ⟨x,y,z,w,hr,hs,he⟩).elim)

/-- A finite alphabet and a uniform finite size bound suffice; no well-order or Choice. -/
theorem bounded_incompatible_finite (hp : LowerPeano σ)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (α → β → γ → Prop)) (hd : FiniteSubset D D)
    (n : (σ → Prop) → Prop) (hn : LowerNat n)
    (U : (α → β → γ → Prop) → Prop)
    (sub : ∀ R, U R → FiniteCondition A B D R ∧ TernaryBound A B D n R)
    (inc : IncompatibleFamily U) : FiniteSubset (FiniteCondition A B D) U := by
  have main := lowerNat_induction
    (fun n => ∀ U : (α → β → γ → Prop) → Prop,
      (∀ R, U R → FiniteCondition A B D R ∧ TernaryBound A B D n R) →
      IncompatibleFamily U → FiniteSubset (FiniteCondition A B D) U)
    (by
      intro U sub _
      apply finiteSubset_single_fibre (FiniteCondition A B D) U (fun R hr => (sub R hr).1)
      intro R S hr hs
      apply rigid_eq_of_coext R S (sub R hr).1.1 (sub S hs).1.1
      intro x y z
      exact ⟨fun h => (ternaryBound_zero_empty hp A B D R (sub R hr).2 x y z h).elim,
        fun h => (ternaryBound_zero_empty hp A B D S (sub S hs).2 x y z h).elim⟩)
    (by
      intro n hn ih U sub inc
      obtain hex | hempty := em (∃ R, U R)
      · obtain ⟨R,hR⟩ := hex
        have fibres : ∀ x y z, R x y z → FiniteSubset (FiniteCondition A B D)
            (fun S => ∃ w, D w ∧ U S ∧ S x y w) := by
          intro x y _ _
          exact finiteSubset_indexed_union D D (FiniteCondition A B D) (fun w S => U S ∧ S x y w) hd
            (fun w _ => bounded_fixed_assignment_finite hp A B D rc n hn ih x y w _
              (fun S h => sub S h.1) (fun S h => h.2)
              (fun S T hS hT hne => inc S T hS.1 hT.1 hne))
        have cover := finiteTernary_indexed_union A B D R (FiniteCondition A B D)
          (fun x y _ S => ∃ w, D w ∧ U S ∧ S x y w) (sub R hR).1.2.1 fibres
        have all := finiteSubset_union (FiniteCondition A B D) (fun S => S = R) _
          (finiteSubset_singleton (FiniteCondition A B D) R (sub R hR).1) cover
        apply finiteSubset_subset (FiniteCondition A B D) _ U all
        intro S hS
        obtain he | hne := em (S = R)
        · exact Or.inl he
        · obtain ⟨x,y,z,w,hr,hs,_⟩ := ternary_conflict_of_not_agree R S
            (inc R S hR hS (fun e => hne e.symm))
          have hw := (finiteTernary_members A B D S (sub S hS).1.2.1 x y w hs).2.2
          exact Or.inr ⟨x,y,z,hr,w,hw,hS,hs⟩
      · exact finiteSubset_empty (FiniteCondition A B D) U (fun R h => hempty ⟨R,h⟩)) n hn
  exact main U sub inc

theorem conditionBit_finite : FiniteSubset ConditionBit ConditionBit :=
  finiteSubset_union ConditionBit (fun p => p = True) (fun p => p = False)
    (finiteSubset_singleton ConditionBit True conditionBit_true)
    (finiteSubset_singleton ConditionBit False conditionBit_false)

theorem cohen_bounded_incompatible_finite (hp : LowerPeano σ) (I : β → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → β → Prop → Prop))
    (n : (σ → Prop) → Prop) (hn : LowerNat n)
    (U : ((((σ → Prop) → Prop) → β → Prop → Prop) → Prop))
    (sub : ∀ R, U R → CohenCondition I R ∧ TernaryBound LowerNat I ConditionBit n R)
    (inc : IncompatibleFamily U) : FiniteSubset (CohenCondition I) U :=
  bounded_incompatible_finite hp LowerNat I ConditionBit rc conditionBit_finite n hn U sub inc

/-- Every antichain splits into finite size-bounded layers; overlaps cause no choice issue. -/
theorem cohen_antichain_layer_finite (hp : LowerPeano σ) (I : β → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → β → Prop → Prop))
    (U : ((((σ → Prop) → Prop) → β → Prop → Prop) → Prop))
    (sub : ∀ R, U R → CohenCondition I R)
    (inc : ∀ R S, U R → U S → R ≠ S →
      ¬ ∃ T, CohenCondition I T ∧ TernaryExtends T R ∧ TernaryExtends T S)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    FiniteSubset (CohenCondition I) (fun R => U R ∧ TernaryBound LowerNat I ConditionBit n R) :=
  cohen_bounded_incompatible_finite hp I rc n hn _
    (fun R h => ⟨sub R h.1,h.2⟩)
    (fun R S hR hS hne hag => inc R S hR.1 hS.1 hne
      ((finiteCondition_compatible_iff LowerNat I ConditionBit rc R S (sub R hR.1) (sub S hS.1)).mpr hag))

theorem cohen_condition_has_bound (I : β → Prop)
    (R : ((σ → Prop) → Prop) → β → Prop → Prop) (hr : CohenCondition I R) :
    ∃ n : (σ → Prop) → Prop, LowerNat n ∧ TernaryBound LowerNat I ConditionBit n R :=
  finiteTernary_has_bound LowerNat I ConditionBit R hr.2.1

#classicism_check ternary_conflict_of_not_agree bounded_incompatible_finite conditionBit_finite cohen_bounded_incompatible_finite cohen_antichain_layer_finite cohen_condition_has_bound
#classicism_types ternary_conflict_of_not_agree bounded_incompatible_finite conditionBit_finite cohen_bounded_incompatible_finite cohen_antichain_layer_finite cohen_condition_has_bound
end Classicism.MathematicalContingency
