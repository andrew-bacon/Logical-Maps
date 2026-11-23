import Classicism.Results.MathematicalContingency.InductiveRigidity

/-!
At every object-language type σ, let ν = (σ → t) → t. This module applies
Goodsell's Lemma 8 to the existing exact-count and at-least-count definitions.
The conclusion concerns the PROPERTY of being a finite cardinality quantifier.
It does not say that an exact-count quantifier has the same truth value on an
arbitrary varying predicate at every world.

Ordinary completeness proves WeaklyRigid; necessary completeness proves the
checkpoint's stronger Rigid. No infinity assumption is needed for either result.
-/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem finiteCardinality_persistent : Persistent (@FiniteCardinality σ _) :=
  inductiveClosure_persistent (ZeroCard σ) SucCard

/-- Exact-count version of Goodsell Lemma 8. -/
theorem finiteCardinality_restricted_barcan
    (bc : BooleanCompleteAt (((σ → Prop) → Prop) → Prop))
    (X : ((σ → Prop) → Prop) → Prop)
    (hx : ∀ n, FiniteCardinality n → □ (X n)) :
    □ (∀ n, FiniteCardinality n → X n) :=
  inductiveClosure_weaklyInextensible (ZeroCard σ) SucCard bc X hx

theorem finiteCardinality_weaklyRigid
    (bc : BooleanCompleteAt (((σ → Prop) → Prop) → Prop)) :
    WeaklyRigid (@FiniteCardinality σ _) :=
  inductiveClosure_weaklyRigid (ZeroCard σ) SucCard bc

theorem finiteCardinality_rigid
    (bc : □ (BooleanCompleteAt (((σ → Prop) → Prop) → Prop))) :
    Rigid (@FiniteCardinality σ _) :=
  inductiveClosure_rigid (ZeroCard σ) SucCard bc

theorem lowerNat_persistent : Persistent (@LowerNat σ _) :=
  inductiveClosure_persistent (AtLeastZero σ) SucCard

/-- The same argument for the at-least naturals used in the CH development. -/
theorem lowerNat_restricted_barcan
    (bc : BooleanCompleteAt (((σ → Prop) → Prop) → Prop))
    (X : ((σ → Prop) → Prop) → Prop)
    (hx : ∀ n, LowerNat n → □ (X n)) :
    □ (∀ n, LowerNat n → X n) :=
  inductiveClosure_weaklyInextensible (AtLeastZero σ) SucCard bc X hx

theorem lowerNat_weaklyRigid
    (bc : BooleanCompleteAt (((σ → Prop) → Prop) → Prop)) :
    WeaklyRigid (@LowerNat σ _) :=
  inductiveClosure_weaklyRigid (AtLeastZero σ) SucCard bc

/-- Supplies the previously explicit rigidN premise, from boxed completeness. -/
theorem lowerNat_rigid
    (bc : □ (BooleanCompleteAt (((σ → Prop) → Prop) → Prop))) :
    Rigid (@LowerNat σ _) :=
  inductiveClosure_rigid (AtLeastZero σ) SucCard bc

#classicism_check finiteCardinality_persistent finiteCardinality_restricted_barcan
  finiteCardinality_weaklyRigid finiteCardinality_rigid lowerNat_persistent
  lowerNat_restricted_barcan lowerNat_weaklyRigid lowerNat_rigid
#classicism_types finiteCardinality_persistent finiteCardinality_restricted_barcan
  finiteCardinality_weaklyRigid finiteCardinality_rigid lowerNat_persistent
  lowerNat_restricted_barcan lowerNat_weaklyRigid lowerNat_rigid

end Classicism.MathematicalContingency
