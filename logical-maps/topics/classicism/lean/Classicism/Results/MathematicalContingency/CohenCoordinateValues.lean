import Classicism.Results.MathematicalContingency.ConeSuprema
import Classicism.Results.MathematicalContingency.PropositionConeTransport

/-!
Cohen coordinates as represented suprema of the True basic cones.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The relation defines all values without choosing a supremum function.
Completion, interval representation and incompatibility preservation are inputs.
-/
namespace Classicism.MathematicalContingency
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]

def CohenCoordinateValue (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (F : β → Prop → Prop) (a : τ) (n : (σ → Prop) → Prop) (p : Prop) : Prop :=
  RepresentedSupremum B R (ConeGenerators (CohenCondition I) C (fun d => d n a True)) F p

/-- Totality holds even outside the coordinate carrier: there the generators
are empty. The downstream name construction only asks for I a and LowerNat n. -/
theorem cohenCoordinateValue_total (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (complete : ∀ X : β → Prop, (∀ x, X x → B x) → ∃ b, Supremum B R X b)
    (maps : Maps C (CohenCondition I) B) (F : β → Prop → Prop) (P : Prop)
    (fmap : Maps F B (Below P)) (a : τ) (n : (σ → Prop) → Prop) :
    ∃ p, CohenCoordinateValue I B R C F a n p :=
  representedSupremum_exists B R complete F P fmap
    (ConeGenerators (CohenCondition I) C (fun d => d n a True))
    (coneGenerators_sub (CohenCondition I) C B maps (fun d => d n a True))

theorem cohenCoordinateValue_functional (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (order : PartialOrderOn B R) (F : β → Prop → Prop) (P : Prop)
    (fmap : Maps F B (Below P)) (a : τ) (n : (σ → Prop) → Prop) (p q : Prop)
    (hp : CohenCoordinateValue I B R C F a n p)
    (hq : CohenCoordinateValue I B R C F a n q) : p = q :=
  representedSupremum_functional B R order F P fmap
    (ConeGenerators (CohenCondition I) C (fun d => d n a True)) p q hp hq

theorem cohenCoordinateValue_laws (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (o : β) (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (maps : Maps C (CohenCondition I) B)
    (incompatible : IncompatibleCones (CohenCondition I)
      (ConditionOrder LowerNat I ConditionBit) B R o C)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False) :
    CohenCoordinateLaws I (RelCompose C F) (CohenCoordinateValue I B R C F) := by
  constructor
  · intro d q n a p hd cone value bit
    exact coneSupremum_positive (CohenCondition I) C B R F P iso
      (fun e => e n a True) p value d q hd bit cone
  · intro d q n a p _ cone value bit
    refine coneSupremum_negative (CohenCondition I) (ConditionOrder LowerNat I ConditionBit)
      C B R o maps incompatible F P iso zero (fun e => e n a True) p value d q cone ?_
    intro e _ he h
    obtain ⟨f,hf,hfd,hfe⟩ := h
    exact cohenCondition_opposite_incompatible I e d n a he bit ⟨f,hf,hfe.2.2,hfd.2.2⟩

/-- Package the exact coordinate inputs expected by the existing Cohen
obstruction, with one fixed composition Cp and one relational value T. -/
theorem cohenCoordinateValue_interfaces (I : τ → Prop)
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (B : β → Prop) (R : β → β → Prop) (o : β)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (cba : CBA B R)
    (cones : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) B R o C)
    (incompatible : IncompatibleCones (CohenCondition I)
      (ConditionOrder LowerNat I ConditionBit) B R o C)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False) :
    PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) (RelCompose C F) P ∧
    P ≠ False ∧ CohenCoordinateLaws I (RelCompose C F) (CohenCoordinateValue I B R C F) ∧
    (∀ a n, I a → LowerNat n → ∃ p, CohenCoordinateValue I B R C F a n p) ∧
    (∀ a n p q, I a → LowerNat n → CohenCoordinateValue I B R C F a n p →
      CohenCoordinateValue I B R C F a n q → p = q) := by
  obtain ⟨hc,hn⟩ := cohen_denseCones_propositionCones I rc B R o C F P cones iso zero
  exact ⟨hc,hn,cohenCoordinateValue_laws I B R o C cones.1 incompatible F P iso zero,
    fun a n _ _ => cohenCoordinateValue_total I B R C cba.2.1 cones.1 F P iso.1.1.1 a n,
    fun a n p q _ _ => cohenCoordinateValue_functional I B R C cba.1 F P iso.1.1.1 a n p q⟩

#classicism_check cohenCoordinateValue_total cohenCoordinateValue_functional
  cohenCoordinateValue_laws cohenCoordinateValue_interfaces
#classicism_types cohenCoordinateValue_total cohenCoordinateValue_functional
  cohenCoordinateValue_laws cohenCoordinateValue_interfaces
end Classicism.MathematicalContingency
