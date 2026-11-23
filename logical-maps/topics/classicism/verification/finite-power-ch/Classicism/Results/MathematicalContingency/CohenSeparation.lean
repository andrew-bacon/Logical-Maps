import Classicism.Results.MathematicalContingency.IndexedNames
import Classicism.Results.MathematicalContingency.NaturalModal
import Classicism.Results.MathematicalContingency.CohenConditions
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ : Type} [Ty σ] [Ty τ]

/-- The propositional images of basic cones. All map laws here are current. -/
def PropositionCones (Q : τ → Prop) (E : τ → τ → Prop) (C : τ → Prop → Prop) (P : Prop) : Prop :=
  Maps C Q (Below P) ∧ (∀ d q, C d q → q ≠ False) ∧
  (∀ d e q r, C d q → C e r → E e d → EntailmentOrder r q) ∧
  (∀ q, q ≠ False → EntailmentOrder q P → ∃ d r, Q d ∧ C d r ∧ EntailmentOrder r q)

/-- Coordinate-cone laws required from the deferred regular-open representation. -/
def CohenCoordinateLaws (I : τ → Prop)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) : Prop :=
  (∀ d q n a p, CohenCondition I d → C d q → T a n p → d n a True → EntailmentOrder q p) ∧
  (∀ d q n a p, CohenCondition I d → C d q → T a n p → d n a False → EntailmentOrder q (¬ p))

theorem distinct_values_not_coext (X Y : τ → Prop) (n : τ) (q : Prop)
    (hx : EntailmentOrder q (X n)) (hy : EntailmentOrder q (¬ Y n)) :
    EntailmentOrder q (¬ (X ≡ Y)) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (hx : q → X n) (hy : q → ¬ Y n) (hq : q) (he : X ≡ Y) => hy hq ((he n).mp (hx hq)))) hx) hy

/-- The fresh-coordinate condition lemma gives dense witnesses of name separation. -/
theorem cohen_names_dense_separation (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) C P)
    (laws : CohenCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (a b : τ) (X Y : ((σ → Prop) → Prop) → Prop)
    (hx : IndexedName LowerNat I T a X) (hy : IndexedName LowerNat I T b Y) (hne : a ≠ b)
    (q : Prop) (hnq : q ≠ False) (hqP : EntailmentOrder q P) :
    ∃ r, r ≠ False ∧ EntailmentOrder r q ∧ EntailmentOrder r (¬ (X ≡ Y)) := by
  obtain ⟨d,s,hd,hds,hsq⟩ := cones.2.2.2 q hnq hqP
  obtain ⟨e,n,he,hn,hed,henA,henB⟩ := cohenCondition_separates hp I rc d hd a b hx.1 hy.1 hne
  obtain ⟨r,_,her⟩ := cones.1.2.1 e he
  obtain ⟨p,htp⟩ := total a n hx.1 hn
  obtain ⟨t,htt⟩ := total b n hy.1 hn
  have hxp : X n = p := hx.2.2 n hn p htp
  have hyt : Y n = t := hy.2.2 n hn t htt
  have hpos : EntailmentOrder r (X n) := hxp.symm ▸ laws.1 e r n a p he her htp henA
  have hneg : EntailmentOrder r (¬ Y n) := hyt.symm ▸ laws.2 e r n b t he her htt henB
  exact ⟨r,cones.2.1 e r her,entailment_trans r s q
    (cones.2.2.1 d e s r hds her ⟨he,hd,hed⟩) hsq,distinct_values_not_coext X Y n r hpos hneg⟩

theorem cohen_names_separate (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) C P)
    (laws : CohenCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (a b : τ) (X Y : ((σ → Prop) → Prop) → Prop)
    (hx : IndexedName LowerNat I T a X) (hy : IndexedName LowerNat I T b Y) (hne : a ≠ b) :
    EntailmentOrder P (¬ (X ≡ Y)) :=
  proposition_density_entailment P (¬ (X ≡ Y))
    (fun q hq hn => cohen_names_dense_separation hp I rc C T P cones laws total a b X Y hx hy hne q hn hq)

theorem nonzero_separation_distinct (P : Prop) (X Y : τ → Prop) (hn : P ≠ False)
    (h : EntailmentOrder P (¬ (X ≡ Y))) : X ≠ Y := by
  intro e
  have hc : □ (X ≡ Y) := e ▸ (nec% (fun _ => (Iff.rfl : X _ ↔ X _)))
  have hf : □ (¬ P) := modal_K _ _ (modal_K _ _
    (nec% (fun (h : P → ¬ (X ≡ Y)) (hc : X ≡ Y) (hp : P) => h hp hc)) h) hc
  exact hn ((box_not_eq P).mp hf)

/-- The name assignment is a current relational bijection; no ND of the indices is used. -/
theorem cohen_names_bijects (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcConditions : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop) (hnP : P ≠ False)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) C P)
    (laws : CohenCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → LowerNat n → T a n p → T a n q → p = q) :
    Bijects (IndexedName LowerNat I T) I (NameCarrier LowerNat I T) :=
  indexedName_bijects LowerNat I T rigidN total
    (fun a ha => indexedName_exists LowerNat I T rcNames rigidN (lowerNat_nd hi) total functional a ha)
    (fun a b X Y hx hy hn => nonzero_separation_distinct P X Y hnP
      (cohen_names_separate (box_elim hi) I rcConditions C T P cones laws total a b X Y hx hy hn))

#classicism_check distinct_values_not_coext cohen_names_dense_separation cohen_names_separate nonzero_separation_distinct cohen_names_bijects
#classicism_types distinct_values_not_coext cohen_names_dense_separation cohen_names_separate nonzero_separation_distinct cohen_names_bijects
end Classicism.MathematicalContingency
