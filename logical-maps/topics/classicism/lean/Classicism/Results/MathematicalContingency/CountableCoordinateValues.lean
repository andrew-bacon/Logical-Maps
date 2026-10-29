import Classicism.Results.MathematicalContingency.CountableBitPreservation
import Classicism.Results.MathematicalContingency.ConeSuprema
import Classicism.Results.MathematicalContingency.PropositionConeTransport

/-!
Countable forcing coordinates as represented suprema of the True basic cones.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The relation defines all values without choosing a supremum function.
Completion, interval representation and incompatibility preservation are inputs.
-/
namespace Classicism.MathematicalContingency
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]

theorem countableBit_opposite_incompatible (I : τ → Prop)
    (d e : CountableBitGraph σ τ) (n : (σ → Prop) → Prop) (a : τ)
    (hd : d n a True) (he : e n a False) :
    ¬ ∃ f, CountableBitCarrier I f ∧ CountableBitOrder I f d ∧ CountableBitOrder I f e := by
  intro ⟨f,hf,hfd,hfe⟩
  exact conditionBit_distinct (hf.2.2.2 n a True False (hfd.2.2 n a True hd) (hfe.2.2 n a False he))

def CountableCoordinateValue (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (F : β → Prop → Prop) (a : τ) (n : (σ → Prop) → Prop) (p : Prop) : Prop :=
  RepresentedSupremum B R (ConeGenerators (CountableBitCarrier I) C (fun d => d n a True)) F p


/-- Totality holds even outside the coordinate carrier: there the generators
are empty. The downstream name construction only asks for I a and LowerNat n. -/
theorem countableCoordinateValue_total (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (complete : ∀ X : β → Prop, (∀ x, X x → B x) → ∃ b, Supremum B R X b)
    (maps : Maps C (CountableBitCarrier I) B) (F : β → Prop → Prop) (P : Prop)
    (fmap : Maps F B (Below P)) (a : τ) (n : (σ → Prop) → Prop) :
    ∃ p, CountableCoordinateValue I B R C F a n p :=
  representedSupremum_exists B R complete F P fmap
    (ConeGenerators (CountableBitCarrier I) C (fun d => d n a True))
    (coneGenerators_sub (CountableBitCarrier I) C B maps (fun d => d n a True))

theorem countableCoordinateValue_functional (I : τ → Prop) (B : β → Prop) (R : β → β → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → β → Prop)
    (order : PartialOrderOn B R) (F : β → Prop → Prop) (P : Prop)
    (fmap : Maps F B (Below P)) (a : τ) (n : (σ → Prop) → Prop) (p q : Prop)
    (hp : CountableCoordinateValue I B R C F a n p)
    (hq : CountableCoordinateValue I B R C F a n q) : p = q :=
  representedSupremum_functional B R order F P fmap
    (ConeGenerators (CountableBitCarrier I) C (fun d => d n a True)) p q hp hq

#classicism_check countableBit_opposite_incompatible countableCoordinateValue_total countableCoordinateValue_functional
#classicism_types countableBit_opposite_incompatible countableCoordinateValue_total countableCoordinateValue_functional
end Classicism.MathematicalContingency
