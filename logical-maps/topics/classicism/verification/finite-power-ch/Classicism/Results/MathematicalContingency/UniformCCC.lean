import Classicism.Results.MathematicalContingency.UniformCoding
import Classicism.Results.MathematicalContingency.FiniteLayerCoding
import Classicism.Results.MathematicalContingency.BoundedAntichains
import Classicism.Results.MathematicalContingency.ConeAntichains
namespace Classicism.MathematicalContingency
variable {σ τ β η : Type} [Ty σ] [Ty τ] [Ty β] [Ty η]

abbrev CohenGraph (σ τ : Type) := ((σ → Prop) → Prop) → τ → Prop → Prop

def CohenCode (I : τ → Prop) (L : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (U : CohenGraph σ τ → Prop) (q : CohenGraph σ τ) (k : (σ → Prop) → Prop) : Prop :=
  LayerCode U L (fun n q => U q ∧ TernaryBound LowerNat I ConditionBit n q) q k

theorem cohenCode_data (I : τ → Prop) (L : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (U : CohenGraph σ τ → Prop) (q : CohenGraph σ τ) (k : (σ → Prop) → Prop)
    (h : CohenCode I L U q k) : U q ∧ LowerNat k :=
  layerCode_data U L (fun n q => U q ∧ TernaryBound LowerNat I ConditionBit n q) q k h

theorem cohenCode_total (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (CohenGraph σ τ))
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop) (U : CohenGraph σ τ → Prop)
    (hw : WellOrderOn (CohenCondition I) L)
    (sub : ∀ q, U q → CohenCondition I q)
    (inc : ∀ q r, U q → U r → q ≠ r →
      ¬ ∃ s, CohenCondition I s ∧ TernaryExtends s q ∧ TernaryExtends s r) (q : CohenGraph σ τ) (hq : U q) :
    ∃ k, LowerNat k ∧ CohenCode I L U q k := by
  apply layerCode_total hp (CohenCondition I) U L
    (fun n q => U q ∧ TernaryBound LowerNat I ConditionBit n q) hw
  · exact fun n hn => cohen_antichain_layer_finite hp I rc U sub inc n hn
  · intro q hq
    obtain ⟨n,hn,hb⟩ := cohen_condition_has_bound I q (sub q hq)
    exact ⟨n,hn,hq,hb⟩
  · exact hq

theorem cohenCode_functional (hp : LowerPeano σ) (I : τ → Prop)
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop) (U : CohenGraph σ τ → Prop)
    (q : CohenGraph σ τ) (k l : (σ → Prop) → Prop)
    (hk : CohenCode I L U q k) (hl : CohenCode I L U q l) : k = l :=
  layerCode_functional hp U L (fun n q => U q ∧ TernaryBound LowerNat I ConditionBit n q) q k l hk hl

theorem cohenCode_injective (hp : LowerPeano σ) (I : τ → Prop)
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop) (U : CohenGraph σ τ → Prop)
    (hw : WellOrderOn (CohenCondition I) L) (sub : ∀ q, U q → CohenCondition I q)
    (q r : CohenGraph σ τ) (k : (σ → Prop) → Prop)
    (hq : CohenCode I L U q k) (hr : CohenCode I L U r k) : q = r :=
  layerCode_injective hp (CohenCondition I) U L
    (fun n q => U q ∧ TernaryBound LowerNat I ConditionBit n q) hw.1
    (fun _ q _ h => sub q h.1) q r k hq hr

theorem cohen_antichain_injects (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (CohenGraph σ τ))
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop) (U : CohenGraph σ τ → Prop)
    (hw : WellOrderOn (CohenCondition I) L)
    (sub : ∀ q, U q → CohenCondition I q)
    (inc : ∀ q r, U q → U r → q ≠ r →
      ¬ ∃ s, CohenCondition I s ∧ TernaryExtends s q ∧ TernaryExtends s r) :
    Injects (CohenCode I L U) U (@LowerNat σ _) :=
  ⟨⟨fun q k h => cohenCode_data I L U q k h,
    fun q hq => cohenCode_total hp I rc L U hw sub inc q hq,
    fun q k l hk hl => cohenCode_functional hp I L U q k l hk hl⟩,
    fun q r k hq hr => cohenCode_injective hp I L U hw sub q r k hq hr⟩

def AntichainCode (I : τ → Prop) (L : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (R : β → β → Prop) (C : CohenGraph σ τ → β → Prop) (U : β → Prop)
    (b : β) (k : (σ → Prop) → Prop) : Prop :=
  RelCompose (LeastCone (CohenCondition I) L R C U)
    (CohenCode I L (SelectedCones (CohenCondition I) L R C U)) b k

theorem selectedCohenCones_injects (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (CohenGraph σ τ))
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : CohenGraph σ τ → β → Prop) (U : β → Prop)
    (hb : PartialOrderOn B R) (hw : WellOrderOn (CohenCondition I) L)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) B R o C)
    (hu : NonzeroAntichain B R o U) :
    Injects (CohenCode I L (SelectedCones (CohenCondition I) L R C U))
      (SelectedCones (CohenCondition I) L R C U) (@LowerNat σ _) := by
  have sub : ∀ q, SelectedCones (CohenCondition I) L R C U q → CohenCondition I q :=
    fun q h => h.elim (fun _ h => h.2.1)
  apply cohen_antichain_injects hp I rc L _ hw sub
  intro q r hq hr hn ⟨s,hs,hsq,hsr⟩
  exact selectedCones_incompatible (CohenCondition I) (ConditionOrder LowerNat I ConditionBit)
    L B R o C U hb hw hc hu q r hq hr hn
    ⟨s,hs,⟨hs,sub q hq,hsq⟩,⟨hs,sub r hr,hsr⟩⟩

theorem booleanAntichain_injects (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (CohenGraph σ τ))
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : CohenGraph σ τ → β → Prop) (U : β → Prop)
    (hb : PartialOrderOn B R) (hw : WellOrderOn (CohenCondition I) L)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) B R o C)
    (hu : NonzeroAntichain B R o U) :
    Injects (AntichainCode I L R C U) U (@LowerNat σ _) :=
  injects_compose _ _ U (SelectedCones (CohenCondition I) L R C U) LowerNat
    (leastCone_bijects (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) L B R o C U
      (cohenCondition_partialOrder I) hb hw hc hu).1
    (selectedCohenCones_injects hp I rc L B R o C U hb hw hc hu)

/-- One ternary relation simultaneously injects every antichain in the family. -/
theorem uniformCCC (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (CohenGraph σ τ))
    (L : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : CohenGraph σ τ → β → Prop)
    (hb : PartialOrderOn B R) (hw : WellOrderOn (CohenCondition I) L)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) B R o C)
    (J : η → Prop) (U : η → β → Prop)
    (hu : ∀ t, J t → NonzeroAntichain B R o (U t)) :
    ∃ T : η → β → ((σ → Prop) → Prop) → Prop,
      ∀ t, J t → Injects (T t) (U t) (@LowerNat σ _) :=
  denseCones_uniform_countable (CohenCondition I) (ConditionOrder LowerNat I ConditionBit)
    L B R o C (cohenCondition_partialOrder I) hb hw hc J U hu
    (cohenFamilies_countable hp I rc L hw J)

#classicism_check cohenCode_data cohenCode_total cohenCode_functional cohenCode_injective cohen_antichain_injects selectedCohenCones_injects booleanAntichain_injects uniformCCC
#classicism_types cohenCode_data cohenCode_total cohenCode_functional cohenCode_injective cohen_antichain_injects selectedCohenCones_injects booleanAntichain_injects uniformCCC
end Classicism.MathematicalContingency
