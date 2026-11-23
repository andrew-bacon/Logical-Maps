import Classicism.Results.MathematicalContingency.CountableCoordinateValues
namespace Classicism.MathematicalContingency
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]
def CountableCoordinateLaws (I : τ → Prop)
    (C : CountableBitGraph σ τ → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) : Prop :=
  (∀ d q n a p, CountableBitCarrier I d → C d q → T a n p → d n a True → EntailmentOrder q p) ∧
  (∀ d q n a p, CountableBitCarrier I d → C d q → T a n p → d n a False → EntailmentOrder q (¬ p))

theorem countableCoordinateValue_laws (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (o : β) (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (maps : Maps C (CountableBitCarrier I) B)
    (incompatible : IncompatibleCones (CountableBitCarrier I)
      (CountableBitOrder I) B R o C)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False) :
    CountableCoordinateLaws I (RelCompose C F) (CountableCoordinateValue I B R C F) := by
  constructor
  · intro d q n a p hd cone value bit
    exact coneSupremum_positive (CountableBitCarrier I) C B R F P iso
      (fun e => e n a True) p value d q hd bit cone
  · intro d q n a p _ cone value bit
    refine coneSupremum_negative (CountableBitCarrier I) (CountableBitOrder I)
      C B R o maps incompatible F P iso zero (fun e => e n a True) p value d q cone ?_
    intro e _ he h
    obtain ⟨f,hf,hfd,hfe⟩ := h
    exact countableBit_opposite_incompatible I e d n a he bit ⟨f,hf,hfe,hfd⟩

/-- Package the exact coordinate inputs expected by the existing Cohen
obstruction, with one fixed composition Cp and one relational value T. -/
theorem countableCoordinateValue_interfaces (I : τ → Prop)
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (B : β → Prop) (R : β → β → Prop) (o : β)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (cba : CBA B R)
    (cones : DenseCones (CountableBitCarrier I) (CountableBitOrder I) B R o C)
    (incompatible : IncompatibleCones (CountableBitCarrier I)
      (CountableBitOrder I) B R o C)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False) :
    PropositionCones (CountableBitCarrier I) (CountableBitOrder I) (RelCompose C F) P ∧
    P ≠ False ∧ CountableCoordinateLaws I (RelCompose C F) (CountableCoordinateValue I B R C F) ∧
    (∀ a n, I a → LowerNat n → ∃ p, CountableCoordinateValue I B R C F a n p) ∧
    (∀ a n p q, I a → LowerNat n → CountableCoordinateValue I B R C F a n p →
      CountableCoordinateValue I B R C F a n q → p = q) := by
  have hc := denseCones_propositionCones (CountableBitCarrier I) (CountableBitOrder I) B R o C F P cones iso zero
  obtain ⟨d,hd,_⟩ := countableCondition_empty (@LowerNat σ _) LowerNat I ConditionBit rc
  have hn := propositionCones_nonzero (CountableBitCarrier I) (CountableBitOrder I) (RelCompose C F) P hc ⟨d,hd⟩
  exact ⟨hc,hn,countableCoordinateValue_laws I B R o C cones.1 incompatible F P iso zero,
    fun a n _ _ => countableCoordinateValue_total I B R C cba.2.1 cones.1 F P iso.1.1.1 a n,
    fun a n p q _ _ => countableCoordinateValue_functional I B R C cba.1 F P iso.1.1.1 a n p q⟩

#classicism_check countableCoordinateValue_laws countableCoordinateValue_interfaces
#classicism_types countableCoordinateValue_laws countableCoordinateValue_interfaces
end Classicism.MathematicalContingency
