import Classicism.Results.Records.Lattice

/-!
# Necessary distinctness and inextensible representatives

Direct source: `research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md`,
§§1–2 (unpaginated original research, `misc`, 22 October 2026).

The optional ND premise is current ND at `t`. Necessary internal separation is
stated explicitly. These reusable lemmas do not assert the complete WRP theorem.
-/

namespace Classicism.Research.InextensiblePower
open Classicism.Paper Classicism.P

theorem persistent_false_step (p : Prop) :
    WeaklyPersistent p → (p ≠ True) → ¬ p := fun hp hn h => hn (hp h)

/-- Current ND prevents a persistent proposition from first becoming true later. -/
theorem nd_persistent_false (nd : NecessityOfDistinctness Prop) (p : Prop)
    (hp : Persistent p) (hn : ¬ p) : □ (¬ p) :=
  modal_K _ _ (modal_K _ _ (nec% (persistent_false_step p)) hp)
    (nd p True (fun he => hn (box_elim he)))

def InternallySeparated {σ : Type} [Ty σ] (P : σ → Prop) : Prop :=
  ∀ a b : σ, P a → P b → a ≠ b → □ (a ≠ b)

def Gap {σ : Type} [Ty σ] (P G : σ → Prop) : Prop :=
  ∃ a : σ, P a ∧ ¬ G a

theorem not_at_of_excludes {σ : Type} [Ty σ] (G : σ → Prop) (a : σ) :
    G ⊆ (fun b => b ≠ a) → ¬ G a := fun h ha => h a ha rfl

/-- WI seals a missing point once the containing relation separates its members. -/
theorem missing_point_sealed {σ : Type} [Ty σ] (P G : σ → Prop)
    (hs : InternallySeparated P) (hi : G ⊆ P) (hg : WeaklyInextensible G)
    (a : σ) (hPa : P a) (hGa : ¬ G a) : □ (¬ G a) :=
  modal_K _ _ (nec% (not_at_of_excludes G a))
    (hg (fun b => b ≠ a) (fun b hb =>
      hs b a (hi b hb) hPa (fun he => hGa (he ▸ hb))))

theorem gap_intro {σ : Type} [Ty σ] (P G : σ → Prop) (a : σ) :
    P a ∧ ¬ G a → Gap P G := fun h => ⟨a, h⟩

theorem gap_step {σ : Type} [Ty σ] (P G : σ → Prop) :
    WeaklyPersistent P → WeaklyInextensible G → InternallySeparated P →
    G ⊆ P → Gap P G → □ (Gap P G) :=
  fun hp hg hs hi h => h.elim fun a ha =>
    modal_K _ _ (nec% (gap_intro P G a))
      ((box_and_eq _ _).mpr ⟨hp a ha.1, missing_point_sealed P G hs hi hg a ha.1 ha.2⟩)

theorem gap_persistent {σ : Type} [Ty σ] (P G : σ → Prop)
    (hp : Persistent P) (hg : Inextensible G)
    (hs : □ (InternallySeparated P)) (hi : G ≤ P) : Persistent (Gap P G) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (modal_K _ _ (nec% (gap_step P G)) hp) hg) hs) ((le_iff G P).1 hi)

theorem not_gap_incl {σ : Type} [Ty σ] (P G : σ → Prop) :
    ¬ Gap P G → P ⊆ G := fun hn a ha =>
  (em (G a)).elim (fun h => h) (fun h => False.elim (hn ⟨a, ha, h⟩))

/-- A persistent, necessarily internally separated relation equals its IC witness.
Only the explicitly supplied separation condition is used at future worlds. -/
theorem separated_coextension_eq {σ : Type} [Ty σ]
    (nd : NecessityOfDistinctness Prop) (P G : σ → Prop)
    (hp : Persistent P) (hs : □ (InternallySeparated P))
    (hg : Inextensible G) (hc : P ≡ G) : P = G := by
  have hgp : G ≤ P := le_of_box_incl
    ((weaklyInextensible_of_inextensible hg) P
      (fun a hGa => (weaklyPersistent_of_persistent hp) a ((hc a).2 hGa)))
  have hgap : Persistent (Gap P G) := gap_persistent P G hp hg hs hgp
  have hn : ¬ Gap P G := fun h => h.elim fun a ha => ha.2 ((hc a).1 ha.1)
  have hpg : P ≤ G := le_of_box_incl
    (modal_K _ _ (nec% (not_gap_incl P G)) (nd_persistent_false nd _ hgap hn))
  exact le_antisymm_rel P G hpg hgp

theorem separated_coextension_rigid {σ : Type} [Ty σ]
    (nd : NecessityOfDistinctness Prop) (P G : σ → Prop)
    (hp : Persistent P) (hs : □ (InternallySeparated P))
    (hg : Inextensible G) (hc : P ≡ G) : Rigid P :=
  ⟨hp, (separated_coextension_eq nd P G hp hs hg hc).symm ▸ hg⟩

theorem curry_product_test {σ : Type} [Ty σ] (P : σ → Prop) (Z : σ → σ → Prop) :
    (∀ a, P a → ∀ b, P b → Z a b) → ∀ a b, P a ∧ P b → Z a b :=
  fun h a b hp => h a hp.1 b hp.2

/-- The square of a weakly rigid property is weakly rigid, without optional axioms. -/
theorem weaklyRigid_square {σ : Type} [Ty σ] (P : σ → Prop) (hp : WeaklyRigid P) :
    WeaklyRigid (fun a b => P a ∧ P b) := by
  refine ⟨fun a b hab => (box_and_eq _ _).mpr ⟨hp.1 a hab.1, hp.1 b hab.2⟩, ?_⟩
  intro Z hz
  exact modal_K _ _ (nec% (curry_product_test P Z))
    (hp.2 (fun a => ∀ b, P b → Z a b)
      (fun a ha => hp.2 (fun b => Z a b) (fun b hb => hz a b ⟨ha, hb⟩)))

def DecidedIdentity {σ : Type} [Ty σ] (a b : σ) : Prop :=
  □ (a = b) ∨ □ (a ≠ b)

theorem decidedIdentity_persistent {σ : Type} [Ty σ] (a b : σ) :
    DecidedIdentity a b → □ (DecidedIdentity a b) :=
  fun h => h.elim
    (fun he => modal_K _ _ (nec% (fun h : □ (a = b) => Or.inl h :
      □ (a = b) → DecidedIdentity a b)) (modal_four _ he))
    (fun hn => modal_K _ _ (nec% (fun h : □ (a ≠ b) => Or.inr h :
      □ (a ≠ b) → DecidedIdentity a b)) (modal_four _ hn))

theorem separated_of_decisions {σ : Type} [Ty σ] (P : σ → Prop) :
    (∀ a b, P a ∧ P b → DecidedIdentity a b) → InternallySeparated P :=
  fun h a b ha hb hn => (h a b ⟨ha, hb⟩).elim
    (fun he => False.elim (hn (box_elim he))) (fun he => he)

/-- Current ND and weak rigidity seal internal separation at every later world. -/
theorem weaklyRigid_separated {σ : Type} [Ty σ]
    (nd : NecessityOfDistinctness Prop) (P : σ → Prop) (hp : WeaklyRigid P) :
    □ (InternallySeparated P) := by
  have ndσ : NecessityOfDistinctness σ :=
    Proofs.modal_b_implies_distinctness_necessary_r
      (Proofs.modal_five_implies_modal_b (Proofs.distinctness_necessary_t_implies_modal_five nd))
  exact modal_K _ _ (nec% (separated_of_decisions P))
    ((weaklyRigid_square P hp).2 (fun a b => DecidedIdentity a b)
      (fun a b _ => decidedIdentity_persistent a b
        ((em (a = b)).elim (fun he => Or.inl (necessity_of_identity a b he))
          (fun hn => Or.inr (ndσ a b hn)))))

/-- The exact local tameness consequence, with current ND and current IC. -/
theorem nd_ic_tame {σ : Type} [Ty σ] :
    NecessityOfDistinctness Prop → InextensibleComprehension (σ → Prop) →
    TameRigidity (σ → Prop) :=
  fun nd ic P hp => (ic P).elim fun G hG =>
    separated_coextension_rigid nd P G (persistent_of_weaklyRigid hp)
      (weaklyRigid_separated nd P hp) hG.1 hG.2

end Classicism.Research.InextensiblePower
