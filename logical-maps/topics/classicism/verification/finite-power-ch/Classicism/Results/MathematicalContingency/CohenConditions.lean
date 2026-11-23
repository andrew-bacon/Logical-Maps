import Classicism.Results.MathematicalContingency.FiniteConditions

/-! Current Cohen conditions on LowerNat x I, as rigid ternary relations.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
No ND assumption for I and no necessary functionality are used. -/
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]

def ConditionBit (p : Prop) : Prop := p = True ∨ p = False

def CohenCondition (I : τ → Prop) (R : ((σ → Prop) → Prop) → τ → Prop → Prop) : Prop :=
  FiniteCondition LowerNat I ConditionBit R

theorem conditionBit_true : ConditionBit True := Or.inl rfl

theorem conditionBit_false : ConditionBit False := Or.inr rfl

theorem conditionBit_distinct : (True : Prop) ≠ False := fun h => h ▸ True.intro

theorem cohenCondition_empty (I : τ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop)) :
    ∃ R : ((σ → Prop) → Prop) → τ → Prop → Prop, CohenCondition I R ∧ TernaryEmpty R := finiteCondition_empty LowerNat I ConditionBit rc

theorem cohenCondition_partialOrder (I : τ → Prop) :
    PartialOrderOn (@CohenCondition σ τ _ _ I) (ConditionOrder LowerNat I ConditionBit) :=
  conditionOrder_partialOrder LowerNat I ConditionBit

theorem cohenCondition_fresh_nat (hp : LowerPeano σ) (I : τ → Prop)
    (R : ((σ → Prop) → Prop) → τ → Prop → Prop) (hr : CohenCondition I R) :
    ∃ n, LowerNat n ∧ ∀ a b, ¬ R n a b := finiteTernary_fresh_nat hp I ConditionBit R hr.2.1

theorem cohenCondition_decides_coordinate (I : τ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (R : ((σ → Prop) → Prop) → τ → Prop → Prop) (hr : CohenCondition I R)
    (n : (σ → Prop) → Prop) (a : τ) (hn : LowerNat n) (ha : I a) :
    ∃ S, CohenCondition I S ∧ TernaryExtends S R ∧ ∃ b, S n a b :=
  finiteCondition_decides_coordinate LowerNat I ConditionBit rc R hr n a hn ha True conditionBit_true

theorem cohenCondition_separates (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (R : ((σ → Prop) → Prop) → τ → Prop → Prop) (hr : CohenCondition I R)
    (a b : τ) (ha : I a) (hb : I b) (hne : a ≠ b) :
    ∃ S n, CohenCondition I S ∧ LowerNat n ∧ TernaryExtends S R ∧ S n a True ∧ S n b False := by
  obtain ⟨n,hn,hfresh⟩ := cohenCondition_fresh_nat hp I R hr
  obtain ⟨T,ht,hi⟩ := finiteCondition_add_fresh LowerNat I ConditionBit rc R hr n a True
    hn ha conditionBit_true (hfresh a)
  have hfree : ∀ p, ¬ T n b p := by
    intro p h
    obtain h | ⟨_,e,_⟩ := (hi n b p).mp h
    · exact hfresh b p h
    · exact hne e.symm
  obtain ⟨S,hs,hj⟩ := finiteCondition_add_fresh LowerNat I ConditionBit rc T ht n b False
    hn hb conditionBit_false hfree
  exact ⟨S,n,hs,hn,fun u v w h => (hj u v w).mpr (Or.inl ((hi u v w).mpr (Or.inl h))),
    (hj n a True).mpr (Or.inl ((hi n a True).mpr (Or.inr ⟨rfl,rfl,rfl⟩))),
    (hj n b False).mpr (Or.inr ⟨rfl,rfl,rfl⟩)⟩

theorem cohenCondition_opposite_incompatible (I : τ → Prop)
    (R S : ((σ → Prop) → Prop) → τ → Prop → Prop)
    (n : (σ → Prop) → Prop) (a : τ) (hr : R n a True) (hs : S n a False) :
    ¬ ∃ T, CohenCondition I T ∧ TernaryExtends T R ∧ TernaryExtends T S := by
  intro ⟨T,ht,he,hf⟩
  exact conditionBit_distinct (ht.2.2 n a True False (he n a True hr) (hf n a False hs))

#classicism_check conditionBit_true conditionBit_false conditionBit_distinct cohenCondition_empty
  cohenCondition_partialOrder cohenCondition_fresh_nat cohenCondition_decides_coordinate
  cohenCondition_separates cohenCondition_opposite_incompatible
#classicism_types conditionBit_true conditionBit_false conditionBit_distinct cohenCondition_empty
  cohenCondition_partialOrder cohenCondition_fresh_nat cohenCondition_decides_coordinate
  cohenCondition_separates cohenCondition_opposite_incompatible
end Classicism.MathematicalContingency
