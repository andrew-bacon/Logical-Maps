import Classicism.Results.Records.Choice

/-!
# A closed-domain Bourbaki–Witt lemma in finitary C

Direct source: `research/2026-10-22/notes/relational-choice-boolean-completeness-transversal-proof.md`,
§5, and `followup/choice-completeness-actuality-audit.md`, canonical-chain audit
(original research, `misc`, 22 October 2026; unpaginated).

This implementation uses the existing proved Lewin core. Its selector on chain
codes is constructed from a unique supremum entity and the given functional
graph. Coextensive codes are never identified. Neither RC, TC, Plenitude, Zorn,
an external ordinal, nor a quotient type is assumed. All order hypotheses are
actual and unboxed. Separate certificate requests are supplied.
-/

namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

/-- The least upper bound is in `P`; the represented family is `A`. -/
def DomainLUB {σ : Type} [Ty σ] (P : σ → Prop) (R : σ → σ → Prop)
    (A : σ → Prop) (u : σ) : Prop :=
  P u ∧ (∀ x, A x → R x u) ∧
    ∀ v, P v → (∀ x, A x → R x v) → R u v

def DomainChainComplete {σ : Type} [Ty σ] (P : σ → Prop) (R : σ → σ → Prop) : Prop :=
  ∀ A : σ → Prop, (∀ x, A x → P x) → TotalOrderOn R A → ∃ u, DomainLUB P R A u

/-- Objects outside `P` form a bottom equivalence class in this preorder. -/
def DomainOrder {σ : Type} [Ty σ] (P : σ → Prop) (R : σ → σ → Prop)
    (x y : σ) : Prop := P x → P y ∧ R x y

theorem chain_coext {σ : Type} [Ty σ] (R : σ → σ → Prop) (A B : σ → Prop)
    (e : ∀ x, A x ↔ B x) (h : TotalOrderOn R A) : TotalOrderOn R B :=
  ⟨fun x y z hx hy hz => h.1 x y z ((e x).2 hx) ((e y).2 hy) ((e z).2 hz),
   fun x y hx hy => h.2.1 x y ((e x).2 hx) ((e y).2 hy),
   fun x y hx hy => h.2.2 x y ((e x).2 hx) ((e y).2 hy)⟩

theorem domainLUB_coext {σ : Type} [Ty σ] (P : σ → Prop) (R : σ → σ → Prop)
    (A B : σ → Prop) (e : ∀ x, A x ↔ B x) (u : σ) (h : DomainLUB P R A u) :
    DomainLUB P R B u :=
  ⟨h.1, fun x hx => h.2.1 x ((e x).2 hx),
   fun v hv hu => h.2.2 v hv (fun x hx => hu x ((e x).1 hx))⟩

theorem domainLUB_unique {σ : Type} [Ty σ] (P : σ → Prop) (R : σ → σ → Prop)
    (ha : ∀ x y, R x y → R y x → x = y) (A : σ → Prop) (u v : σ)
    (hu : DomainLUB P R A u) (hv : DomainLUB P R A v) : u = v :=
  ha u v (hu.2.2 v hv.1 hv.2.1) (hv.2.2 u hu.1 hu.2.1)

/-- On chains use `f(sup(C ∩ P))`; elsewhere use the fixed default `b`.
This is a represented graph, not a choice operation. -/
def SupStep {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop) (b : σ)
    (C : σ → Prop) (x : σ) : Prop :=
  (TotalOrderOn (DomainOrder P R) C ∧
    ∃ u, DomainLUB P R (fun y => C y ∧ P y) u ∧ f u x) ∨
  (¬ TotalOrderOn (DomainOrder P R) C ∧ x = b)

theorem supStep_coext {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop)
    (b : σ) (C D : σ → Prop) (e : ∀ y, C y ↔ D y) (x : σ) :
    SupStep P R f b C x → SupStep P R f b D x := by
  intro h
  rcases h with h | h
  · obtain ⟨u, hu, hux⟩ := h.2
    exact Or.inl ⟨chain_coext _ C D e h.1,
      u, domainLUB_coext P R _ _
        (fun y => ⟨fun h => ⟨(e y).1 h.1, h.2⟩,
          fun h => ⟨(e y).2 h.1, h.2⟩⟩) u hu, hux⟩
  · exact Or.inr ⟨fun hD => h.1 (chain_coext _ D C (fun y => (e y).symm) hD), h.2⟩

theorem supStep_unique {σ : Type} [Ty σ] (P : σ → Prop) (R f : σ → σ → Prop)
    (b : σ) (ha : ∀ x y, R x y → R y x → x = y)
    (hf : ∀ u x y, P u → f u x → f u y → x = y)
    (C : σ → Prop) (x y : σ) (hx : SupStep P R f b C x)
    (hy : SupStep P R f b C y) : x = y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · obtain ⟨u, hu, hux⟩ := hx.2
    obtain ⟨v, hv, hvy⟩ := hy.2
    have e := domainLUB_unique P R ha _ u v hu hv
    rw [← e] at hvy
    exact hf u x y hu.1 hux hvy
  · exact (hy.1 hx.1).elim
  · exact (hx.1 hy.1).elim
  · exact hx.2.trans hy.2.symm

/-- The bottom quotient preorder's chains restrict to actual chains inside `P`. -/
theorem domain_chain_restrict {σ : Type} [Ty σ] (P : σ → Prop) (R : σ → σ → Prop)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (C : σ → Prop) (h : TotalOrderOn (DomainOrder P R) C) :
    TotalOrderOn R (fun x => C x ∧ P x) :=
  ⟨fun x y z _ _ _ => ht x y z,
   fun x y _ _ => ha x y,
   fun x y hx hy => (h.2.2 x y hx.1 hy.1).elim
     (fun hxy => Or.inl (hxy hx.2).2) (fun hyx => Or.inr (hyx hy.2).2)⟩

/-- An actual total functional progressive graph on a represented chain-complete
domain in an antisymmetric order has a fixed point. The empty chain is included. -/
theorem domain_graph_fixedpoint {σ : Type} [Ty σ]
    (P : σ → Prop) (R f : σ → σ → Prop) (b : σ)
    (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (hc : DomainChainComplete P R)
    (hserial : ∀ x, P x → ∃ y, f x y)
    (hclosed : ∀ x y, P x → f x y → P y)
    (hprog : ∀ x y, P x → f x y → R x y)
    (huniq : ∀ x y z, P x → f x y → f x z → y = z) :
    ∃ x, P x ∧ f x x := by
  refine (em (∃ x, P x ∧ f x x)).elim id (fun hn => False.elim ?_)
  have dr : ∀ x, DomainOrder P R x x := fun x hx => ⟨hx, hr x⟩
  have dt : ∀ x y z, DomainOrder P R x y → DomainOrder P R y z →
      DomainOrder P R x z := fun x y z hxy hyz hx =>
    ⟨(hyz (hxy hx).1).1, ht x y z (hxy hx).2 (hyz (hxy hx).1).2⟩
  have total : ∀ C, ∃ x, SupStep P R f b C x := by
    intro C
    refine (em (TotalOrderOn (DomainOrder P R) C)).elim (fun hC => ?_)
      (fun hC => ⟨b, Or.inr ⟨hC, rfl⟩⟩)
    obtain ⟨u, hu⟩ := hc (fun y => C y ∧ P y) (fun _ h => h.2)
      (domain_chain_restrict P R ht ha C hC)
    obtain ⟨x, hux⟩ := hserial u hu.1
    exact ⟨x, Or.inl ⟨hC, u, hu, hux⟩⟩
  have strict : ∀ C x, SupStep P R f b C x → TotalOrderOn (DomainOrder P R) C →
      ∀ y, C y → DomainOrder P R y x ∧ ¬ DomainOrder P R x y := by
    intro C x hx hC y hy
    rcases hx with hx | hx
    · obtain ⟨u, hu, hux⟩ := hx.2
      have px := hclosed u x hu.1 hux
      have ux := hprog u x hu.1 hux
      have nback : ¬ R x u := fun hxu =>
        hn ⟨u, hu.1, (ha x u hxu ux) ▸ hux⟩
      exact ⟨fun py => ⟨px, ht y u x (hu.2.1 y ⟨hy, py⟩) ux⟩,
        fun hxy => nback (ht x y u (hxy px).2 (hu.2.1 y ⟨hy, (hxy px).1⟩))⟩
    · exact (hx.1 hC).elim
  exact Proofs.lewin_core (R := DomainOrder P R) (F := SupStep P R f b)
    dt (supStep_coext P R f b) (supStep_unique P R f b ha huniq) dr total strict

/-- Operation form, only where an operation into `σ` is admitted. -/
theorem domain_operation_fixedpoint {σ : Type} [Rel σ]
    (P : σ → Prop) (R : σ → σ → Prop) (g : σ → σ) (b : σ)
    (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (ha : ∀ x y, R x y → R y x → x = y)
    (hc : DomainChainComplete P R)
    (hclosed : ∀ x, P x → P (g x))
    (hprog : ∀ x, P x → R x (g x)) : ∃ x, P x ∧ g x = x :=
  domain_graph_fixedpoint P R (fun x y => g x = y) b hr ht ha hc
    (fun x _ => ⟨g x, rfl⟩)
    (fun x y hx e => e ▸ hclosed x hx)
    (fun x y hx e => e ▸ hprog x hx)
    (fun _ _ _ _ e₁ e₂ => e₁.symm.trans e₂)

end Classicism.Research.Choice
