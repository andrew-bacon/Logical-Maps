import Classicism.Results.MathematicalContingency.ModalLemmas

/-! Density in an algebra represented by a propositional interval yields entailment.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
The representation remains relational; no necessary functionality is inferred. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem entailment_counterexample_false (p q : Prop) :
    EntailmentOrder p q ↔ (p ∧ ¬ q) = False := by
  constructor
  · intro h
    exact (box_not_eq _).mp (modal_K _ _
      (nec% (fun (h : p → q) (hc : p ∧ ¬ q) => hc.2 (h hc.1))) h)
  · intro h
    exact modal_K _ _ (nec% (fun (hn : ¬ (p ∧ ¬ q)) (hp : p) =>
      (em q).elim id (fun hq => (hn ⟨hp,hq⟩).elim))) ((box_not_eq _).mpr h)

/-- The elementary propositional argument; density is current and nonzero means not False. -/
theorem proposition_density_entailment (p φ : Prop)
    (dense : ∀ q, EntailmentOrder q p → q ≠ False →
      ∃ r, r ≠ False ∧ EntailmentOrder r q ∧ EntailmentOrder r φ) :
    EntailmentOrder p φ := by
  apply (entailment_counterexample_false p φ).mpr
  obtain hz | hn := em ((p ∧ ¬ φ) = False)
  · exact hz
  · obtain ⟨r,hr,hrq,hrφ⟩ := dense (p ∧ ¬ φ) (nec% (fun h : p ∧ ¬ φ => h.1)) hn
    have hf : □ (¬ r) := modal_K _ _ (modal_K _ _
      (nec% (fun (h1 : r → p ∧ ¬ φ) (h2 : r → φ) (h : r) => (h1 h).2 (h2 h))) hrq) hrφ
    exact (hr ((box_not_eq r).mp hf)).elim

/-- A zero representative is supplied by current surjectivity alone. -/
theorem intervalIso_zero_exists (A : σ → Prop) (E : σ → σ → Prop)
    (F : σ → Prop → Prop) (p : Prop)
    (hf : OrderIso F A E (Below p) EntailmentOrder) :
    ∃ z, A z ∧ F z False :=
  hf.1.2.2 False (nec% (fun h : False => (h.elim : p)))

theorem intervalIso_zero_iff (A : σ → Prop) (E : σ → σ → Prop)
    (F : σ → Prop → Prop) (p : Prop)
    (hf : OrderIso F A E (Below p) EntailmentOrder)
    (z b : σ) (q : Prop) (hz : F z False) (hb : F b q) :
    b = z ↔ q = False := by
  constructor
  · intro e
    exact hf.1.1.1.2.2 b q False hb (e.symm ▸ hz)
  · intro e
    exact hf.1.1.2 b z False (e ▸ hb) hz

/-- Density below a fixed algebra element gives entailment by its current image. -/
theorem density_to_entailment_below (A : σ → Prop) (E : σ → σ → Prop)
    (F : σ → Prop → Prop) (p φ : Prop)
    (hf : OrderIso F A E (Below p) EntailmentOrder)
    (z b₀ : σ) (q₀ : Prop) (hz : F z False) (hb₀ : F b₀ q₀)
    (dense : ∀ b, A b → b ≠ z → E b b₀ →
      ∃ c r, A c ∧ c ≠ z ∧ E c b ∧ F c r ∧ EntailmentOrder r φ) :
    EntailmentOrder q₀ φ := by
  apply proposition_density_entailment q₀ φ
  intro q hq hnq
  have hqp : Below p q := modal_K _ _ (modal_K _ _
    (nec% (fun (h1 : q → q₀) (h2 : q₀ → p) (h : q) => h2 (h1 h))) hq)
    (hf.1.1.1.1 b₀ q₀ hb₀).2
  obtain ⟨b,hb,hbq⟩ := hf.1.2.2 q hqp
  have hn : b ≠ z := fun he => hnq ((intervalIso_zero_iff A E F p hf z b q hz hbq).mp he)
  obtain ⟨c,r,_,hc,hcb,hcr,hrφ⟩ := dense b hb hn ((hf.2 b b₀ q q₀ hbq hb₀).mpr hq)
  exact ⟨r,(fun he => hc ((intervalIso_zero_iff A E F p hf z c r hz hcr).mpr he)),
    (hf.2 c b r q hcr hbq).mp hcb,hrφ⟩

/-- The paper's density-to-entailment lemma. No completeness or modal map law is needed. -/
theorem density_to_entailment (A : σ → Prop) (E : σ → σ → Prop)
    (F : σ → Prop → Prop) (p φ : Prop)
    (hf : OrderIso F A E (Below p) EntailmentOrder)
    (z : σ) (hz : F z False)
    (dense : ∀ b, A b → b ≠ z →
      ∃ c r, A c ∧ c ≠ z ∧ E c b ∧ F c r ∧ EntailmentOrder r φ) :
    EntailmentOrder p φ := by
  obtain ⟨b,_,hb⟩ := hf.1.2.2 p (nec% (fun h : p => h))
  exact density_to_entailment_below A E F p φ hf z b p hz hb
    (fun c hc hn _ => dense c hc hn)

#classicism_check entailment_counterexample_false proposition_density_entailment
  intervalIso_zero_exists intervalIso_zero_iff density_to_entailment_below density_to_entailment
#classicism_types entailment_counterexample_false proposition_density_entailment
  intervalIso_zero_exists intervalIso_zero_iff density_to_entailment_below density_to_entailment
end Classicism.MathematicalContingency
