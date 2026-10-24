import Classicism.Principles.Choice
import Classicism.Principles.Lattice

/-!
# Completeness and disjoint joins

Direct source: `research/2026-10-22/followup/choice-completeness-actuality.md`,
§§1–3 (original research, `misc`, 22 October 2026; unpaginated).

All premises are actual and unboxed. These are finitary shallow C proofs, pending
the separate gate, relational-type, and object-language certificate checks.
No inference below identifies a material union with an algebraic supremum.
-/

namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

/-- Evaluation has the haecceity-implication right adjoint, without BF. -/
theorem evaluation_adjunction {σ : Type} [Ty σ] (F : σ → Prop) (x : σ) (p : Prop) :
    F ≤ (fun z => z = x → p) ↔ F x ≤ p := by
  constructor
  · intro h
    exact le_of_box_incl (modal_K _ _
      (nec% (fun (h : ∀ z, F z → z = x → p) (hx : F x) => h x hx rfl))
      ((le_iff _ _).1 h))
  · intro h
    exact le_of_box_incl (modal_K _ _
      (nec% (fun (h : F x → p) (z : σ) (hz : F z) (e : z = x) => h (e ▸ hz)))
      ((le_iff_prop _ _).1 h))

/-- The supremum equation after evaluation. The family remains represented by `A`. -/
theorem evaluation_lub {σ : Type} [Ty σ] (A : (σ → Prop) → Prop)
    (J : σ → Prop) (hJ : LUB J A) (x : σ) (p : Prop) :
    (∀ F, A F → F x ≤ p) ↔ J x ≤ p := by
  constructor
  · intro h
    exact (evaluation_adjunction J x p).1 ((hJ _).1
      (fun F hF => (evaluation_adjunction F x p).2 (h F hF)))
  · intro h F hF
    exact le_trans_prop _ _ _
      (le_apply_of_le F J x (((hJ J).2 (le_refl_arrow_prop J)) F hF)) h

/-- The literal represented evaluation image has the expected supremum. -/
theorem evaluation_image_lub {σ : Type} [Ty σ] (A : (σ → Prop) → Prop)
    (J : σ → Prop) (hJ : LUB J A) (x : σ) :
    LUB (J x) (fun p => ∃ F, A F ∧ p = F x) := by
  intro p
  constructor
  · intro h
    exact (evaluation_lub A J hJ x p).1 (fun F hF => h (F x) ⟨F, hF, rfl⟩)
  · intro h q hq
    obtain ⟨F, hF, e⟩ := hq
    rw [e]
    exact (evaluation_lub A J hJ x p).2 h F hF

/-- `BC_tt` supplies `BC_t`, by constant properties evaluated at `True`. -/
theorem completeness_tt_to_t : BooleanCompleteness (Prop → Prop) →
    BooleanCompleteness Prop := by
  intro bc
  apply BooleanCompleteness.of_lub
  intro X
  let A : (Prop → Prop) → Prop := fun F => ∃ p, X p ∧ F = (fun _ : Prop => p)
  obtain ⟨J, hJ⟩ := BooleanCompleteness.to_lub bc A
  refine ⟨J True, fun q => ⟨?_, ?_⟩⟩
  · intro h
    apply (evaluation_lub A J hJ True q).1
    intro F hF
    obtain ⟨p, hp, e⟩ := hF
    rw [e]
    exact h p hp
  · intro h p hp
    exact (evaluation_lub A J hJ True q).2 h (fun _ => p) ⟨p, hp, rfl⟩

theorem curry_le (p q r : Prop) : (p ∧ q) ≤ r → p ≤ (q → r) := fun h =>
  le_of_box_incl (modal_K _ _
    (nec% (fun (h : (p ∧ q) → r) (hp : p) (hq : q) => h ⟨hp, hq⟩))
    ((le_iff_prop _ _).1 h))

theorem uncurry_le (p q r : Prop) : p ≤ (q → r) → (p ∧ q) ≤ r := fun h =>
  le_of_box_incl (modal_K _ _
    (nec% (fun (h : p → q → r) (hpq : p ∧ q) => h hpq.1 hpq.2))
    ((le_iff_prop _ _).1 h))

theorem swap_le (p q r : Prop) : p ≤ (q → r) → q ≤ (p → r) := fun h =>
  le_of_box_incl (modal_K _ _
    (nec% (fun (h : p → q → r) (hq : q) (hp : p) => h hp hq))
    ((le_iff_prop _ _).1 h))

/-- Two applications of evaluation's supremum equation. -/
theorem lub_pair_closed {σ : Type} [Ty σ] (A : (σ → Prop) → Prop)
    (J : σ → Prop) (hJ : LUB J A) (x y : σ) (r : Prop)
    (h : ∀ F G, A F → A G → (F x ∧ G y) ≤ r) : (J x ∧ J y) ≤ r := by
  apply uncurry_le
  apply (evaluation_lub A J hJ x (J y → r)).1
  intro F hF
  apply swap_le
  apply (evaluation_lub A J hJ y (F x → r)).1
  intro G hG
  exact swap_le _ _ _ (curry_le _ _ _ (h F G hF hG))

def HaecFamily {σ : Type} [Ty σ] (A : σ → Prop) : (σ → Prop) → Prop :=
  fun F => ∃ a, A a ∧ F = (fun z => z = a)

theorem haec_join_value {σ : Type} [Ty σ] (A J : σ → Prop)
    (hJ : LUB J (HaecFamily A)) (a : σ) (ha : A a) : □ (J a) := by
  have h : (a = a) ≤ J a := le_apply_of_le (fun z : σ => z = a) J a
    (((hJ J).2 (le_refl_arrow_prop J)) _ ⟨a, ha, rfl⟩)
  exact modal_K _ _ ((le_iff_prop _ _).1 h) (nec% (Eq.refl a))

theorem haec_substitution {σ : Type} [Ty σ] (R : σ → σ → Prop) (a b x y : σ) :
    R a b → (x = a ∧ y = b) → R x y := by
  intro h e
  rw [e.1, e.2]
  exact h

/-- A stable binary relation on the seeds persists across the haecceity join. -/
theorem haec_join_closed {σ : Type} [Ty σ] (A J : σ → Prop)
    (hJ : LUB J (HaecFamily A)) (R : σ → σ → Prop)
    (hR : ∀ a b, A a → A b → □ (R a b)) (x y : σ) :
    (J x ∧ J y) ≤ R x y := by
  apply lub_pair_closed (HaecFamily A) J hJ x y
  intro F G hF hG
  obtain ⟨a, ha, eF⟩ := hF
  obtain ⟨b, hb, eG⟩ := hG
  rw [eF, eG]
  exact le_of_box_incl (modal_K _ _ (nec% (haec_substitution R a b x y))
    (hR a b ha hb))

def Compatible (p q : Prop) : Prop := p = q ∨ (p ∧ q) = False

theorem compatible_box (p q : Prop) : Compatible p q → □ (Compatible p q) :=
  fun h => h.elim
    (fun e => modal_K _ _
      (nec% (fun (e : p = q) => (Or.inl e : Compatible p q)))
      (necessity_of_identity _ _ e))
    (fun e => modal_K _ _
      (nec% (fun (e : (p ∧ q) = False) => (Or.inr e : Compatible p q)))
      (necessity_of_identity _ _ e))

theorem disjoint_le_neg (p q : Prop) (h : (p ∧ q) = False) : p ≤ ¬ q :=
  le_of_box_incl (modal_K _ _
    (nec% (fun (e : (p ∧ q) = False) (hp : p) (hq : q) => e ▸ And.intro hp hq))
    (necessity_of_identity _ _ h))

theorem swap_neg_le (p q : Prop) (h : p ≤ ¬ q) : q ≤ ¬ p :=
  le_of_box_incl (modal_K _ _
    (nec% (fun (h : p → ¬ q) (hq : q) (hp : p) => h hp hq))
    ((le_iff_prop _ _).1 h))

/-- Higher-type completeness reflects truth through a disjoint algebraic join.
Zero seeds are allowed. No choice premise occurs. -/
theorem false_disjoint_lub_false (bc : BooleanCompleteness (Prop → Prop))
    (A : Prop → Prop) (j : Prop) (hj : LUB j A)
    (hf : ∀ a, A a → ¬ a)
    (hd : ∀ a b, A a → A b → Compatible a b) : ¬ j := by
  obtain ⟨J, hJ⟩ := BooleanCompleteness.to_lub bc (HaecFamily A)
  have closed := haec_join_closed A J hJ Compatible
    (fun a b ha hb => compatible_box a b (hd a b ha hb))
  let v : Prop := ∀ p, J p → ¬ p
  have hja : ∀ a, A a → a ≤ ¬ v := by
    intro a ha
    apply swap_neg_le
    exact le_of_box_incl (modal_K _ _
      (nec% (fun (hJa : J a) (hv : ∀ p, J p → ¬ p) => hv a hJa))
      (haec_join_value A J hJ a ha))
  intro hjtrue
  have hnv : ¬ v := imp_of_le_prop _ _ ((hj (¬ v)).1 hja) hjtrue
  have hex : ∃ q, J q ∧ q := (em (∃ q, J q ∧ q)).elim id fun hn =>
    (hnv (fun q hq hqt => hn ⟨q, hq, hqt⟩)).elim
  obtain ⟨q, hJq, hq⟩ := hex
  have hupper : UB (¬ q) A := by
    intro a ha
    have hc : Compatible q a := imp_of_le_prop _ _ (closed q a)
      ⟨hJq, box_elim (haec_join_value A J hJ a ha)⟩
    rcases hc with e | e
    · exact ((hf a ha) (e ▸ hq)).elim
    · exact swap_neg_le _ _ (disjoint_le_neg _ _ e)
  exact (imp_of_le_prop _ _ ((hj (¬ q)).1 hupper) hjtrue) hq

theorem disjoint_lub_truth (bc : BooleanCompleteness (Prop → Prop))
    (A : Prop → Prop) (j : Prop) (hj : LUB j A)
    (hd : ∀ a b, A a → A b → Compatible a b) :
    j ↔ ∃ a, A a ∧ a := by
  constructor
  · intro ht
    exact (em (∃ a, A a ∧ a)).elim id fun hn =>
      (false_disjoint_lub_false bc A j hj (fun a ha h => hn ⟨a, ha, h⟩) hd ht).elim
  · intro h
    obtain ⟨a, ha, ht⟩ := h
    exact imp_of_le_prop _ _ (((hj j).2 (le_refl_prop j)) a ha) ht

/-- A true meet of the actual truths is precisely an Actuality witness. -/
theorem truth_meet_actuality (m : Prop) (hm : GLB m (fun p : Prop => p)) :
    Actuality ↔ m := by
  constructor
  · intro h
    obtain ⟨w, hw, hwl⟩ := h
    exact imp_of_le_prop _ _ ((hm w).1 hwl) hw
  · intro ht
    exact ⟨m, ht, (hm m).2 (le_refl_prop m)⟩

theorem truth_meet_false_eq_bot (m : Prop) (hm : GLB m (fun p : Prop => p))
    (h : ¬ m) : m = False :=
  eq_false_of_le_neg m (((hm m).2 (le_refl_prop m)) (¬ m) h)

/-- Failure of Actuality supplies a nonzero false part of any nonzero proposition. -/
theorem false_part_of_not_actuality (hn : ¬ Actuality) (b : Prop) (hb : b ≠ False) :
    ∃ c, ¬ c ∧ c ≠ False ∧ c ≤ b := by
  refine (em b).elim (fun ht => ?_) (fun hf => ⟨b, hf, hb, le_refl_prop b⟩)
  have hex : ∃ q, q ∧ ¬ b ≤ q := (em (∃ q, q ∧ ¬ b ≤ q)).elim id fun h =>
    (hn ⟨b, ht, fun q hq => (em (b ≤ q)).elim id fun hle => (h ⟨q, hq, hle⟩).elim⟩).elim
  obtain ⟨q, hq, hnle⟩ := hex
  refine ⟨b ∧ ¬ q, (fun h => h.2 hq), ?_, and_le_left_prop _ _⟩
  intro e
  have hle : b ≤ ¬ ¬ q := disjoint_le_neg b (¬ q) e
  rw [not_not_eq] at hle
  exact hnle hle

end Classicism.Research.Choice
