import Classicism.Results.Research.ChoiceCompleteness
import Classicism.Results.Research.ChoiceFixedPoint

/-!
# The guarded RC + BC argument for Actuality

Direct source: `research/2026-10-22/followup/choice-completeness-actuality.md`,
§§2–5 (original research, `misc`, 22 October 2026; unpaginated).

The guarded operation route is first proved from actual `RC_(tt,t)` and `BC_tt`.
The final theorem sharpens it to `RC_(t,t)` by indexing the selector by the
unique propositional join of the current antichain. This refinement was obtained
while translating the proof; its direct source is this module and
`research/2026-10-22/lean-formalization/choice-join-indexed-refinement.md`.
The language remains the original finitary relational language. Supremum and
graph-functionality hypotheses are never necessitated.
-/

namespace Classicism.Research.Choice
open Classicism.Paper Classicism.P

def FalseNonzero (p : Prop) : Prop := ¬ p ∧ p ≠ False

/-- An algebraically bounded property with pointwise necessary compatibility.
The two proposition quantifiers remain outside the modal/algebraic condition. -/
def GuardedAntichain (F : Prop → Prop) : Prop :=
  F ≤ FalseNonzero ∧ ∀ p q, (F p ∧ F q) ≤ Compatible p q

theorem and_mono_le (p q r s : Prop) (hpr : p ≤ r) (hqs : q ≤ s) :
    (p ∧ q) ≤ (r ∧ s) :=
  le_and_prop _ _ _
    (le_trans_prop _ _ _ (and_le_left_prop p q) hpr)
    (le_trans_prop _ _ _ (and_le_right_prop p q) hqs)

theorem neg_mono_le (p q : Prop) (h : p ≤ q) : (¬ q) ≤ (¬ p) :=
  le_of_box_incl (modal_K _ _
    (nec% (fun (h : p → q) (hnq : ¬ q) (hp : p) => hnq (h hp)))
    ((le_iff_prop _ _).1 h))

theorem disjoint_of_le_neg (p q : Prop) (h : p ≤ ¬ q) : (p ∧ q) = False :=
  (box_not_eq _).mp (modal_K _ _
      (nec% (fun (h : p → ¬ q) (hpq : p ∧ q) => h hpq.1 hpq.2))
      ((le_iff_prop _ _).1 h))

theorem guarded_member (F : Prop → Prop) (hF : GuardedAntichain F) (p : Prop)
    (hp : F p) : FalseNonzero p := incl_of_le hF.1 p hp

theorem guarded_pair (F : Prop → Prop) (hF : GuardedAntichain F) (p q : Prop)
    (hp : F p) (hq : F q) : Compatible p q :=
  imp_of_le_prop _ _ (hF.2 p q) ⟨hp, hq⟩

/-- Completeness closes the guarded domain under represented chain suprema. -/
theorem guarded_chain_lub (C : (Prop → Prop) → Prop) (J : Prop → Prop)
    (hJ : LUB J C) (hC : ∀ F, C F → GuardedAntichain F)
    (hc : TotalOrderOn (fun F G : Prop → Prop => F ≤ G) C) : GuardedAntichain J := by
  refine ⟨(hJ FalseNonzero).1 (fun F hF => (hC F hF).1), ?_⟩
  intro p q
  apply lub_pair_closed C J hJ p q
  intro F G hF hG
  rcases hc.2.2 F G hF hG with hFG | hGF
  · exact le_trans_prop _ _ _
      (and_mono_le _ _ _ _ (le_apply_of_le F G p hFG) (le_refl_prop (G q)))
      ((hC G hG).2 p q)
  · exact le_trans_prop _ _ _
      (and_mono_le _ _ _ _ (le_refl_prop (F p)) (le_apply_of_le G F q hGF))
      ((hC F hF).2 p q)

theorem guarded_chain_complete (bc : BooleanCompleteness (Prop → Prop)) :
    DomainChainComplete GuardedAntichain (fun F G : Prop → Prop => F ≤ G) := by
  intro C hC hc
  obtain ⟨J, hJ⟩ := BooleanCompleteness.to_lub bc C
  exact ⟨J, guarded_chain_lub C J hJ hC hc,
    (hJ J).2 (le_refl_arrow_prop J), fun G _ hu => (hJ G).1 hu⟩

def FalseStep (F : Prop → Prop) (a : Prop) : Prop :=
  ¬ a ∧ a ≠ False ∧ ∀ q, F q → (a ∧ q) = False

/-- A fresh false proposition can be adjoined to any guarded antichain. -/
theorem guarded_step_exists (bc : BooleanCompleteness (Prop → Prop))
    (hn : ¬ Actuality) (F : Prop → Prop) (hF : GuardedAntichain F) :
    ∃ a, FalseStep F a := by
  obtain ⟨j, hj⟩ := BooleanCompleteness.to_lub (completeness_tt_to_t bc) F
  have hjf : ¬ j := false_disjoint_lub_false bc F j hj
    (fun a ha => (guarded_member F hF a ha).1)
    (fun a b ha hb => guarded_pair F hF a b ha hb)
  have hnzero : (¬ j) ≠ False := fun e => e ▸ hjf
  obtain ⟨a, haf, hanz, haj⟩ := false_part_of_not_actuality hn (¬ j) hnzero
  refine ⟨a, haf, hanz, fun q hq => ?_⟩
  exact disjoint_of_le_neg a q (le_trans_prop _ _ _ haj
    (neg_mono_le q j (((hj j).2 (le_refl_prop j)) q hq)))

/-- Actual selector edges are guarded *inside* the extending property. -/
def GuardNew (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop) (p : Prop) : Prop :=
  S F p ∧ (∀ r, S F r → r = p) ∧ FalseNonzero p ∧
    ∀ q, F q → Compatible p q ∧ Compatible q p

def GuardGrow (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop) : Prop → Prop :=
  fun p => F p ∨ GuardNew S F p

theorem grow_progressive (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop) :
    F ≤ GuardGrow S F :=
  le_of_box_incl (nec% (fun (p : Prop) (hp : F p) =>
    (Or.inl hp : GuardGrow S F p)))

theorem grow_bound_imp (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop) :
    (∀ p, F p → FalseNonzero p) → ∀ p, GuardGrow S F p → FalseNonzero p :=
  fun h p hp => hp.elim (h p) (fun hn => hn.2.2.1)

/-- Both orientations of compatibility are explicit guards. This avoids treating
commutativity of a Boolean identity as an unconditional H theorem. -/
theorem grow_pair_imp (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop) (p q : Prop) :
    (F p ∧ F q → Compatible p q) →
    (GuardGrow S F p ∧ GuardGrow S F q → Compatible p q) := by
  intro h hpq
  rcases hpq.1 with hp | hp <;> rcases hpq.2 with hq | hq
  · exact h ⟨hp, hq⟩
  · exact (hq.2.2.2 p hp).2
  · exact (hp.2.2.2 q hq).1
  · exact Or.inl (hp.2.1 q hq.1).symm

theorem grow_preserves (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop)
    (hF : GuardedAntichain F) : GuardedAntichain (GuardGrow S F) :=
  ⟨le_of_box_incl (modal_K _ _ (nec% (grow_bound_imp S F)) ((le_iff _ _).1 hF.1)),
   fun p q => le_of_box_incl (modal_K _ _ (nec% (grow_pair_imp S F p q))
     ((le_iff_prop _ _).1 (hF.2 p q)))⟩

theorem step_not_member (F : Prop → Prop) (a : Prop) (ha : FalseStep F a) : ¬ F a := by
  intro hFa
  have e := ha.2.2 a hFa
  rw [and_self_eq] at e
  exact ha.2.1 e

theorem selected_guard_new (S : (Prop → Prop) → Prop → Prop) (F : Prop → Prop)
    (a : Prop) (hSa : S F a) (hu : ∀ r, S F r → a = r) (ha : FalseStep F a) :
    GuardNew S F a := by
  refine ⟨hSa, (fun r hr => (hu r hr).symm), ⟨ha.1, ha.2.1⟩, ?_⟩
  intro q hq
  have e := ha.2.2 q hq
  refine ⟨Or.inr e, Or.inr ?_⟩
  rw [and_comm_eq]
  exact e

theorem grow_strict (S : (Prop → Prop) → Prop → Prop)
    (hSf : Functional S)
    (hS : ∀ F a, S F a → GuardedAntichain F → FalseStep F a)
    (F : Prop → Prop) (hF : GuardedAntichain F) : GuardGrow S F ≠ F := by
  obtain ⟨a, hSa, hu⟩ := hSf F
  have ha := hS F a hSa hF
  have hg : GuardGrow S F a := Or.inr (selected_guard_new S F a hSa hu ha)
  intro e
  exact step_not_member F a ha (congrFun e a ▸ hg)

theorem guarded_selector_impossible (bc : BooleanCompleteness (Prop → Prop))
    (S : (Prop → Prop) → Prop → Prop) (hSf : Functional S)
    (hS : ∀ F a, S F a → GuardedAntichain F → FalseStep F a) : False := by
  obtain ⟨F, hF, hfix⟩ := domain_operation_fixedpoint GuardedAntichain
    (fun F G : Prop → Prop => F ≤ G) (GuardGrow S) (fun _ => False)
    le_refl_arrow_prop le_trans_arrow le_antisymm_arrow (guarded_chain_complete bc)
    (grow_preserves S) (fun F _ => grow_progressive S F)
  exact grow_strict S hSf hS F hF hfix

/-- Actual Relational Choice at `(tt,t)` and actual completeness at `tt` imply
Actuality. No stronger, boxed conclusion is silently substituted. -/
theorem choice_completeness_actuality :
    RelationalChoice (Prop → Prop) Prop → BooleanCompleteness (Prop → Prop) → Actuality := by
  intro rc bc
  refine (em Actuality).elim id (fun hn => False.elim ?_)
  let U : (Prop → Prop) → Prop → Prop :=
    fun F a => GuardedAntichain F → FalseStep F a
  have hser : Serial U := by
    intro F
    exact (em (GuardedAntichain F)).elim
      (fun hF => (guarded_step_exists bc hn F hF).elim fun a ha => ⟨a, fun _ => ha⟩)
      (fun hnF => ⟨False, fun hF => (hnF hF).elim⟩)
  obtain ⟨S, hSf, hSU⟩ := rc U hser
  exact guarded_selector_impossible bc S hSf hSU

theorem necessary_choice_completeness_actuality :
    NecRelationalChoice (Prop → Prop) Prop → NecBooleanCompleteness (Prop → Prop) →
      NecActuality := fun rc bc =>
  modal_K _ _ (modal_K _ _ (nec% choice_completeness_actuality) rc) bc

/-- The only additional choice instance selects from properties of `σ`. -/
theorem choice_completeness_transversal {σ : Type} [Ty σ] :
    RelationalChoice (Prop → Prop) Prop → BooleanCompleteness (Prop → Prop) →
    RelationalChoice (σ → Prop) σ → TransversalChoice σ := fun rc bc rcσ =>
  Proofs.transversal_and_relational_choice_imply_transversal_choice
    (Proofs.actuality_implies_transversal (choice_completeness_actuality rc bc)) rcσ

theorem prop_lub_unique (F : Prop → Prop) (j k : Prop)
    (hj : LUB j F) (hk : LUB k F) : j = k :=
  le_antisymm_prop j k ((hj k).1 ((hk k).2 (le_refl_prop k)))
    ((hk j).1 ((hj j).2 (le_refl_prop j)))

/-- An actual selector on propositions suffices: select a false part outside
the unique propositional supremum of each guarded antichain. No operation
representing either the supremum relation or the selector is needed. -/
theorem choice_completeness_actuality_sharp :
    RelationalChoice Prop Prop → BooleanCompleteness (Prop → Prop) → Actuality := by
  intro rc bc
  refine (em Actuality).elim id (fun hn => False.elim ?_)
  let U : Prop → Prop → Prop :=
    fun j a => ¬ j → ¬ a ∧ a ≠ False ∧ a ≤ ¬ j
  have hu : Serial U := by
    intro j
    refine (em (¬ j)).elim (fun hj => ?_)
      (fun hj => ⟨False, fun h => (hj h).elim⟩)
    have hnj : (¬ j) ≠ False := fun e => e ▸ hj
    obtain ⟨a, ha⟩ := false_part_of_not_actuality hn (¬ j) hnj
    exact ⟨a, fun _ => ha⟩
  obtain ⟨T, hTf, hTU⟩ := rc U hu
  let S : (Prop → Prop) → Prop → Prop :=
    fun F a => ∃ j, LUB j F ∧ T j a
  have hSf : Functional S := by
    intro F
    obtain ⟨j, hj⟩ := BooleanCompleteness.to_lub (completeness_tt_to_t bc) F
    obtain ⟨a, hTa, huniq⟩ := hTf j
    refine ⟨a, ⟨j, hj, hTa⟩, ?_⟩
    intro b hb
    obtain ⟨k, hk, hTb⟩ := hb
    have e := prop_lub_unique F k j hk hj
    rw [e] at hTb
    exact huniq b hTb
  have hs : ∀ F a, S F a → GuardedAntichain F → FalseStep F a := by
    intro F a hSa hF
    obtain ⟨j, hj, hTa⟩ := hSa
    have hjf : ¬ j := false_disjoint_lub_false bc F j hj
      (fun p hp => (guarded_member F hF p hp).1)
      (fun p q hp hq => guarded_pair F hF p q hp hq)
    have ha := hTU j a hTa hjf
    refine ⟨ha.1, ha.2.1, ?_⟩
    intro q hq
    exact disjoint_of_le_neg a q (le_trans_prop _ _ _ ha.2.2
      (neg_mono_le q j (((hj j).2 (le_refl_prop j)) q hq)))
  exact guarded_selector_impossible bc S hSf hs

theorem necessary_choice_completeness_actuality_sharp :
    NecRelationalChoice Prop Prop → NecBooleanCompleteness (Prop → Prop) →
      NecActuality := fun rc bc =>
  modal_K _ _ (modal_K _ _ (nec% choice_completeness_actuality_sharp) rc) bc

/-- In particular, all-type RC and completeness only at `tt` imply all-type TC. -/
theorem choice_completeness_transversal_sharp {σ : Type} [Ty σ] :
    RelationalChoice Prop Prop → BooleanCompleteness (Prop → Prop) →
    RelationalChoice (σ → Prop) σ → TransversalChoice σ := fun rc bc rcσ =>
  Proofs.transversal_and_relational_choice_imply_transversal_choice
    (Proofs.actuality_implies_transversal (choice_completeness_actuality_sharp rc bc)) rcσ

end Classicism.Research.Choice
