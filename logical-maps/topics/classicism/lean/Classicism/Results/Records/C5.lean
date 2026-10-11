import Classicism.Paper
import Classicism.Principles
import Classicism.Results.Records.Coarse
import Classicism.Results.Records.Lattice
import Classicism.Results.Records.Choice

/-!
# Proofs of map records: `C5`: `□ND` at `t`

The records whose premises include `□ND_t`, the theory `C5` (Classicism, §§2.1–2.3):
Propositions 2.3, 2.4, 2.6, 2.10, 2.12, 2.14, 2.16, n. 41, and Proposition 2.11 reduced
to a restriction principle.
The conventions are in `Results/Records.lean`.
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-! ### `C5`: `□ND` at `t` (Classicism, §§2.1–2.3)

`C5` is `C` with `□ND`, equivalently `□5` or `□B` (Proposition 2.2). The records below take
`□ND_t` (`NecNecessityOfDistinctnessT`) as the `C5` premise: from `ND_t`, `B` follows
(`modal_five_implies_modal_b`), and from `B`, `ND` at every type (Prior); so `□ND_t`
gives `B`, `□B`, and `ND`, `□ND` at every type. Helper lemmas are stated unfolded, so
that the audits do not read them as records. -/

/-- `ND_t` gives `B`. -/
theorem b_of_nd_t : (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → ∀ p : Prop, p → □ ◇ p :=
  fun nd => modal_five_implies_modal_b (distinctness_necessary_t_implies_modal_five nd)

/-- `□ND_t` gives `□B`. -/
theorem box_b_of_box_nd_t :
    □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → □ (∀ p : Prop, p → □ ◇ p) :=
  modal_K _ _ (nec% b_of_nd_t)

/-- With `B`, `◇□p → p`: otherwise `¬p`, so `□◇¬p` by `B`, which is `□¬□p`, and `□p` is
`⊥`, against `◇□p`. -/
theorem b_dia_box_imp : (∀ p : Prop, p → □ ◇ p) → ∀ p : Prop, ◇ □ p → p := fun b p hd =>
  (em p).elim id fun hn => by
    have h1 : (◇ (¬ p)) = True := b (¬ p) hn
    have h3 : (□ p) = False :=
      calc (□ p) = ¬ ¬ □ p := (not_not_eq _).symm
        _ = ¬ True := by rw [← dia_not_eq, h1]
        _ = False := not_true_eq
    exact (hd h3).elim

/-- `∀x. ◇□Fx → Fx`, from `B`. -/
theorem b_forall_dia_box_imp {σ : Type} [Ty σ] (F : σ → Prop) :
    (∀ p : Prop, p → □ ◇ p) → ∀ x, ◇ □ (F x) → F x := fun b x => b_dia_box_imp b (F x)

/-- `G ⊆ F` and `∀x. Gx` give `∀x. Fx`. -/
theorem forall_imp_forall {σ : Type} [Ty σ] (G F : σ → Prop) :
    G ⊆ F → (∀ x, G x) → ∀ x, F x := fun h g x => h x (g x)

/-- `necessary-nd-implies-bf` (Proposition 2.3; Prior, and the
proof Prior attributes to Lemmon): from `∀x. □Fx`, `B` gives `□◇∀x. □Fx`; inside the box
`◇∀ → ∀◇` gives `∀x. ◇□Fx`, and the necessitation of `B` in the form `◇□p → p` gives
`∀x. Fx`. -/
theorem necessary_nd_implies_bf {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → Barcan σ := fun hnd F hF =>
  have hb : ∀ p : Prop, p → □ ◇ p := b_of_nd_t (box_elim hnd)
  have h1 : □ (∀ x, ◇ □ (F x)) :=
    modal_K _ _ (nec% (dia_forall_imp (λ x ↦ □ (F x)))) (hb _ hF)
  have h2 : □ (∀ x, ◇ □ (F x) → F x) :=
    modal_K _ _ (nec% (b_forall_dia_box_imp F)) (box_b_of_box_nd_t hnd)
  modal_K _ _ (modal_K _ _ (nec% (forall_imp_forall (λ x ↦ ◇ □ (F x)) F)) h2) h1

/-- `necessary-distinctness-necessary-t-implies-distinctness-necessary-r`: `B`, then
Prior's argument. -/
theorem necessary_distinctness_necessary_t_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecNecessityOfDistinctnessT → NecessityOfDistinctness σ := fun hnd =>
  modal_b_implies_distinctness_necessary_r (b_of_nd_t (box_elim hnd))

/-- `ND_t` gives `ND` at `σ`, unfolded, for necessitation. -/
theorem nd_of_nd_t {σ : Type} [Ty σ] :
    (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → ∀ x y : σ, x ≠ y → □ (x ≠ y) := fun nd =>
  modal_b_implies_distinctness_necessary_r (b_of_nd_t nd)

/-- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r`: the
last record necessitated. -/
theorem necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r
    {σ : Type} [Ty σ] : NecNecessityOfDistinctnessT → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (nd_of_nd_t (σ := σ)))

/-- `□ND_t` gives `BF` at `σ`, unfolded, for necessitation. -/
theorem bf_of_box_nd_t {σ : Type} [Ty σ] :
    □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x) :=
  necessary_nd_implies_bf

/-- `necessary-distinctness-necessary-r-implies-necessary-barcan-r`: Proposition 2.3
necessitated, with `4`. -/
theorem necessary_distinctness_necessary_r_implies_necessary_barcan_r {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → NecBarcan σ := fun hnd =>
  modal_K _ _ (nec% (bf_of_box_nd_t (σ := σ))) (modal_four _ hnd)

/-- `x = y` makes anything follow from `x ≠ y`. -/
theorem eq_imp_ne_imp {σ : Type} [Ty σ] (x y : σ) (q : Prop) : x = y → x ≠ y → q :=
  fun h hne => (hne h).elim

/-- With `ND` at `σ`, each instance of `ND` is necessary: if `x = y`, `NI` makes the
antecedent necessarily false; if not, `ND` and `4` make the consequent necessary. -/
theorem box_nd_instance {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y)) (x y : σ) :
    □ (x ≠ y → □ (x ≠ y)) :=
  (em (x = y)).elim
    (fun h => modal_K _ _ (nec% (eq_imp_ne_imp x y (□ (x ≠ y)))) (necessity_of_identity x y h))
    (fun h => modal_K _ _ (nec% (imp_intro' (x ≠ y) (□ (x ≠ y)))) (modal_four _ (nd x y h)))

/-- `nd-and-bf-imply-necessary-nd`
(Proposition 2.4): each instance of `ND` is necessary, and `BF`, twice, boxes the two
quantifiers. -/
theorem nd_and_bf_imply_necessary_nd
    {σ : Type} [Ty σ] : NecessityOfDistinctness σ → Barcan σ → NecNecessityOfDistinctness σ :=
  fun nd bf => bf (λ x ↦ ∀ y, x ≠ y → □ (x ≠ y))
    (fun x => bf (λ y ↦ x ≠ y → □ (x ≠ y)) (fun y => box_nd_instance nd x y))

/-- `distinctness-necessary-t-and-barcan-t-imply-necessary-distinctness-necessary-t`
(Proposition 2.4 at `t`). -/
theorem distinctness_necessary_t_and_barcan_t_imply_necessary_distinctness_necessary_t :
    NecessityOfDistinctnessT → BarcanT → NecNecessityOfDistinctnessT :=
  nd_and_bf_imply_necessary_nd

/-! In `C5` persistence is inextensibility (Classicism, n. 41). -/

/-- `◇¬q` and `q → □q` give `¬q`. -/
theorem not_of_dia_not_of_persist (q : Prop) : ◇ (¬ q) → (q → □ q) → ¬ q := fun hd hp hq => by
  rw [dia_not_eq] at hd
  exact hd (hp hq)

/-- With `B` and `BF` at `σ`, a persistent property is weakly inextensible (n. 41): if
`∀z. Yz → □Zz`, then for each `z`, either `Yz`, and `□Zz`, or `¬Yz`, and `B` with
persistence make `□¬Yz`; either way `□(Yz → Zz)`, and `BF` boxes the quantifier. -/
theorem weaklyInextensible_of_persistent_b_bf {σ : Type} [Ty σ] (Y : σ → Prop) :
    (∀ p : Prop, p → □ ◇ p) → (∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x)) →
      Persistent Y → WeaklyInextensible Y := fun b bf hP Z hZ =>
  bf (λ z ↦ Y z → Z z) fun z =>
    (em (Y z)).elim
      (fun hy => box_imp_of_box (Y z) (Z z) (hZ z hy))
      (fun hn => box_imp_of_box_not (Y z) (Z z)
        (modal_K _ _ (modal_K _ _ (nec% (not_of_dia_not_of_persist (Y z))) (b _ hn))
          (converse_barcan (λ z ↦ Y z → □ (Y z)) hP z)))

/-- In `C5` a persistent property is inextensible: the last lemma necessitated, with `□B`,
`□BF` and `4` for persistence. -/
theorem inextensible_of_persistent_c5 {σ : Type} [Ty σ]
    (hnd : □ (∀ x y : Prop, x ≠ y → □ (x ≠ y))) (Y : σ → Prop) (hP : Persistent Y) :
    Inextensible Y :=
  modal_K _ _ (modal_K _ _ (modal_K _ _ (nec% (weaklyInextensible_of_persistent_b_bf Y))
    (box_b_of_box_nd_t hnd)) (necessary_distinctness_necessary_r_implies_necessary_barcan_r hnd))
    (modal_four _ hP)

/-- `c5-and-actuality-imply-rigid-comprehension` (Proposition 2.10), at `σ → t`, its list
form being the map's record: Actuality gives a persistent coextension, `λy. w ≤ Xy`
(n. 38), and in `C5` it is inextensible. -/
theorem c5_and_actuality_imply_rigid_comprehension
    {σ : Type} [Ty σ] :
    Actuality → NecNecessityOfDistinctness Prop → RigidComprehension (σ → Prop) := fun act hnd X =>
  act.elim fun w (hw : ActualWorld w) =>
    ⟨_, ⟨(persistent_coext_of_actual_world w hw X).1,
      inextensible_of_persistent_c5 hnd _ (persistent_coext_of_actual_world w hw X).1⟩,
     (persistent_coext_of_actual_world w hw X).2⟩

/-- `c5-and-actuality-imply-completeness` (at type `t` only)
(Proposition 2.5, right to left), at `t`: Propositions 2.10 and 2.8. -/
theorem c5_and_actuality_imply_completeness_at_t :
    Actuality → NecNecessityOfDistinctness Prop → BooleanCompleteness Prop := fun act hnd =>
  rigid_comprehension_r_implies_boolean_completeness_r_at_t
    (c5_and_actuality_imply_rigid_comprehension act hnd)

/-! Boolean Completeness gives Plenitude in `C5` (Proposition 2.14, n. 48). For `R`
functional, let `F_R X := ∀y p. Ryp → Xy ≤ p`, and `G` the greatest lower bound of the
upper bounds of `F_R`, which is its least upper bound. At each `a`, with `Ra pₐ`: the
property `λx. x = a ∧ pₐ` satisfies `F_R` (by `ND`), so it is below `G`, and `pₐ ≤ Ga`;
and `λx. x ≠ a ∨ pₐ` is an upper bound of `F_R` (by `ND` and `BF`), so `G` is below it,
and `Ga ≤ pₐ`. -/

/-- `y ≠ a` refutes `y = a ∧ p`. -/
theorem ne_imp_and_imp {σ : Type} [Ty σ] (y a : σ) (p q : Prop) : y ≠ a → (y = a ∧ p) → q :=
  fun hne h => (hne h.1).elim

/-- `λx. x = a ∧ pₐ` satisfies `F_R`, given `ND`. -/
theorem haec_and_le {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y))
    (R : σ → Prop → Prop) (a : σ) (pa : Prop) (huniq : ∀ z, R a z → pa = z) :
    ∀ y p, R y p → (y = a ∧ pa) ≤ p := fun y p hRy =>
  (em (y = a)).elim
    (fun h => by
      rw [h] at hRy ⊢
      rw [← huniq p hRy]
      exact and_le_right_prop (a = a) pa)
    (fun h => (le_iff_prop _ _).2 (modal_K _ _ (nec% (ne_imp_and_imp y a pa p)) (nd y a h)))

/-- So `pₐ ≤ Ga`. -/
theorem pa_le_of {σ : Type} [Ty σ] (a : σ) (pa : Prop) (G : σ → Prop)
    (h : (λ x ↦ x = a ∧ pa) ≤ G) : pa ≤ G a :=
  le_trans_prop pa (a = a ∧ pa) (G a)
    (le_and_prop pa (a = a) pa ((le_iff_prop _ _).2 (nec% (fun (_ : pa) => (rfl : a = a))))
      (le_refl_prop pa))
    (le_apply_of_le _ G a h)

/-- `(q → p) → q → r ∨ p`. -/
theorem imp_or_right' (q p r : Prop) : (q → p) → q → r ∨ p := fun h hq => Or.inr (h hq)

/-- `r → q → r ∨ p`. -/
theorem imp_or_left' (r q p : Prop) : r → q → r ∨ p := fun h _ => Or.inl h

/-- `λx. x ≠ a ∨ pₐ` is an upper bound of `F_R`, given `ND` and `BF`. -/
theorem ne_or_ub {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y))
    (bf : ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (R : σ → Prop → Prop) (a : σ) (pa : Prop) (hRa : R a pa) :
    ∀ X : σ → Prop, (∀ y p, R y p → X y ≤ p) → X ≤ (λ x ↦ x ≠ a ∨ pa) :=
  fun X hX => (le_iff X _).2 (bf (λ x ↦ X x → x ≠ a ∨ pa) fun x =>
    (em (x = a)).elim
      (fun h => by
        rw [h]
        exact modal_K _ _ (nec% (imp_or_right' (X a) pa (a ≠ a))) ((le_iff_prop _ _).1 (hX a pa hRa)))
      (fun h => modal_K _ _ (nec% (imp_or_left' (x ≠ a) (X x) pa)) (nd x a h)))

/-- `a ≠ a ∨ p` gives `p`. -/
theorem ne_self_or_imp {σ : Type} [Ty σ] (a : σ) (p : Prop) : (a ≠ a ∨ p) → p :=
  fun h => h.elim (fun hne => (hne rfl).elim) id

/-- So `Ga ≤ pₐ`. -/
theorem ga_le_of {σ : Type} [Ty σ] (a : σ) (pa : Prop) (G : σ → Prop)
    (h : G ≤ (λ x ↦ x ≠ a ∨ pa)) : G a ≤ pa :=
  le_trans_prop (G a) (a ≠ a ∨ pa) pa (le_apply_of_le G _ a h)
    ((le_iff_prop _ _).2 (nec% (ne_self_or_imp a pa)))

/-- `c5-and-completeness-imply-plenitude` (for output type `t` only)
(Proposition 2.14), for relations of type `σ → t → t`: Boolean Completeness at `σ → t`
gives the least upper bound `G` of `F_R`, and `Ga = pₐ` at every `a`. -/
theorem c5_and_completeness_imply_plenitude_at_t
    {σ : Type} [Ty σ] :
    BooleanCompleteness (σ → Prop) → NecNecessityOfDistinctness Prop → Plenitude σ Prop :=
  fun bc hnd R hR =>
    have nd := nd_of_nd_t (σ := σ) (box_elim hnd)
    have bf := bf_of_box_nd_t (σ := σ) hnd
    (bc (λ Y ↦ UB Y (λ X ↦ ∀ y p, R y p → X y ≤ p))).elim fun G hG =>
      ⟨G, fun a => (hR a).elim fun pa hpa =>
        have e : pa = G a := le_antisymm_prop pa (G a)
          (pa_le_of a pa G (glb_ub_upper _ G hG _ (haec_and_le nd R a pa hpa.2)))
          (ga_le_of a pa G (glb_ub_least _ G hG _ (ne_or_ub nd bf R a pa hpa.1)))
        e ▸ hpa.1⟩

/-! The same at every output type, for relations `σ → (σ' → t) → t`, pointwise in `σ'`:
its list form in `σ'` is the record at `σs' ⇒* t`, every relational output type, `t`
itself the empty list. The record at `t` above stays for `c5_and_completeness_imply_actuality`. -/

/-- `y ≠ a` refutes `y = a ∧ Pz`. -/
theorem ne_imp_haec {σ σ' : Type} [Ty σ] [Ty σ'] (y a : σ) (Pa P : σ' → Prop) :
    y ≠ a → ∀ z, (y = a ∧ Pa z) → P z :=
  fun hne z h => (hne h.1).elim

/-- `λxz. x = a ∧ Pₐz` satisfies `F_R`, given `ND`. -/
theorem haec_and_le₂ {σ σ' : Type} [Ty σ] [Ty σ'] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y))
    (R : σ → (σ' → Prop) → Prop) (a : σ) (Pa : σ' → Prop) (huniq : ∀ P, R a P → Pa = P) :
    ∀ y P, R y P → (λ z ↦ y = a ∧ Pa z) ≤ P := fun y P hRy =>
  (em (y = a)).elim
    (fun h => by
      rw [h] at hRy ⊢
      rw [← huniq P hRy]
      exact (le_iff _ _).2 (nec% (fun (z : σ') (hz : a = a ∧ Pa z) => hz.2)))
    (fun h => (le_iff _ _).2 (modal_K _ _ (nec% (ne_imp_haec y a Pa P)) (nd y a h)))

/-- `(∀xz. x = a ∧ Pₐz → Gxz) → ∀z. Pₐz → Gaz`. -/
theorem pa_imp_of {σ σ' : Type} [Ty σ] [Ty σ'] (a : σ) (Pa : σ' → Prop) (G : σ → σ' → Prop) :
    (∀ x z, (x = a ∧ Pa z) → G x z) → ∀ z, Pa z → G a z :=
  fun h z hz => h a z ⟨rfl, hz⟩

/-- So `Pₐ ≤ Ga`. -/
theorem pa_le_of₂ {σ σ' : Type} [Ty σ] [Ty σ'] (a : σ) (Pa : σ' → Prop) (G : σ → σ' → Prop)
    (h : (λ x z ↦ x = a ∧ Pa z) ≤ G) : Pa ≤ G a :=
  (le_iff _ _).2 (modal_K _ _ (nec% (pa_imp_of a Pa G)) ((le_iff _ _).1 h))

/-- `(∀z. Xaz → Pₐz) → ∀z. Xaz → a ≠ a ∨ Pₐz`. -/
theorem imp_ne_or_right {σ σ' : Type} [Ty σ] [Ty σ'] (X : σ → σ' → Prop) (a : σ)
    (Pa : σ' → Prop) : (∀ z, X a z → Pa z) → ∀ z, X a z → a ≠ a ∨ Pa z :=
  fun h z hz => Or.inr (h z hz)

/-- `x ≠ a → ∀z. Xxz → x ≠ a ∨ Pₐz`. -/
theorem imp_ne_or_left {σ σ' : Type} [Ty σ] [Ty σ'] (X : σ → σ' → Prop) (x a : σ)
    (Pa : σ' → Prop) : x ≠ a → ∀ z, X x z → x ≠ a ∨ Pa z :=
  fun h _ _ => Or.inl h

/-- `λxz. x ≠ a ∨ Pₐz` is an upper bound of `F_R`, given `ND` and `BF`. -/
theorem ne_or_ub₂ {σ σ' : Type} [Ty σ] [Ty σ'] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y))
    (bf : ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (R : σ → (σ' → Prop) → Prop) (a : σ) (Pa : σ' → Prop) (hRa : R a Pa) :
    ∀ X : σ → σ' → Prop, (∀ y P, R y P → X y ≤ P) → X ≤ (λ x z ↦ x ≠ a ∨ Pa z) :=
  fun X hX => (le_iff X _).2 (bf (λ x ↦ ∀ z, X x z → x ≠ a ∨ Pa z) fun x =>
    (em (x = a)).elim
      (fun h => by
        rw [h]
        exact modal_K _ _ (nec% (imp_ne_or_right X a Pa)) ((le_iff _ _).1 (hX a Pa hRa)))
      (fun h => modal_K _ _ (nec% (imp_ne_or_left X x a Pa)) (nd x a h)))

/-- `(∀xz. Gxz → x ≠ a ∨ Pₐz) → ∀z. Gaz → Pₐz`. -/
theorem ga_imp_of {σ σ' : Type} [Ty σ] [Ty σ'] (a : σ) (Pa : σ' → Prop) (G : σ → σ' → Prop) :
    (∀ x z, G x z → x ≠ a ∨ Pa z) → ∀ z, G a z → Pa z :=
  fun h z hz => (h a z hz).elim (fun hne => (hne rfl).elim) id

/-- So `Ga ≤ Pₐ`. -/
theorem ga_le_of₂ {σ σ' : Type} [Ty σ] [Ty σ'] (a : σ) (Pa : σ' → Prop) (G : σ → σ' → Prop)
    (h : G ≤ (λ x z ↦ x ≠ a ∨ Pa z)) : G a ≤ Pa :=
  (le_iff _ _).2 (modal_K _ _ (nec% (ga_imp_of a Pa G)) ((le_iff _ _).1 h))

/-- `c5-and-completeness-imply-plenitude` (Proposition 2.14), for relations
`σ → (σ' → t) → t`, its list form in `σ'` being the map's record: the argument at `t`,
pointwise in `σ'`. -/
theorem c5_and_completeness_imply_plenitude {σ' σ : Type} [Ty σ'] [Ty σ] :
    BooleanCompleteness (σ → σ' → Prop) → NecNecessityOfDistinctness Prop →
      Plenitude σ (σ' → Prop) :=
  fun bc hnd R hR =>
    have nd := nd_of_nd_t (σ := σ) (box_elim hnd)
    have bf := bf_of_box_nd_t (σ := σ) hnd
    (bc (λ Y ↦ UB Y (λ X ↦ ∀ y P, R y P → X y ≤ P))).elim fun G hG =>
      ⟨G, fun a => (hR a).elim fun Pa hPa =>
        have e : Pa = G a := le_antisymm_arrow Pa (G a)
          (pa_le_of₂ a Pa G (glb_ub_upper _ G hG _ (haec_and_le₂ nd R a Pa hPa.2)))
          (ga_le_of₂ a Pa G (glb_ub_least₂ _ G hG _ (ne_or_ub₂ nd bf R a Pa hPa.1)))
        e ▸ hPa.1⟩

/-- `c5-and-completeness-imply-actuality`
(Proposition 2.5, left to right): Boolean Completeness at `t → t` gives Plenitude at
`t → t` (Proposition 2.14), and Plenitude gives Actuality (Proposition 2.15). -/
theorem c5_and_completeness_imply_actuality :
    BooleanCompleteness (Prop → Prop) → NecNecessityOfDistinctness Prop → Actuality := fun bc hnd =>
  plenitude_r_implies_actuality
    (c5_and_completeness_imply_plenitude_at_t bc hnd)

/-! Atomicity is `□`Actuality and `□`Boolean Completeness in `C5` (Proposition 2.6). -/

/-- `atomicity-t-and-necessary-distinctness-necessary-t-imply-necessary-actuality`
(Proposition 2.6, left to right): Proposition 2.7, with `BF_t` from Proposition 2.3. -/
theorem atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality :
    AtomicityT → NecNecessityOfDistinctnessT → NecActuality := fun at_ hnd =>
  atomicity_t_and_bf_imply_necessary_actuality at_
    (necessary_nd_implies_bf hnd)

/-- Actuality and `□ND_t` give Boolean Completeness at `t`, unfolded, for necessitation. -/
theorem bc_of_actuality_box_nd_t :
    Actuality → □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → BooleanCompleteness Prop :=
  c5_and_actuality_imply_completeness_at_t

/-- `necessary-actuality-and-necessary-distinctness-necessary-t-imply-necessary-boolean-completeness-r`,
at `t`: Proposition 2.5 necessitated, with `4`. -/
theorem necessary_actuality_and_necessary_distinctness_necessary_t_imply_necessary_boolean_completeness_r :
    NecActuality → NecNecessityOfDistinctnessT → NecBooleanCompleteness Prop := fun hna hnd =>
  modal_K _ _ (modal_K _ _ (nec% bc_of_actuality_box_nd_t) hna) (modal_four _ hnd)

/-- The actual world, inside the diamond: `x ∧ w ∧ ∀q. q → w ≤ q` gives `w ≤ x`. -/
theorem le_of_actual_and (x w : Prop) : (x ∧ ActualWorld w) → w ≤ x :=
  fun h => h.2.2 x h.1

/-- A true proposition entailing every truth is non-bottom and decides every proposition. -/
theorem decides_of_actual (x w : Prop) :
    (x ∧ ActualWorld w) → (¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) :=
  fun h => ⟨fun e => e ▸ h.2.1, fun z => (em z).elim (fun hz => Or.inl (h.2.2 z hz))
    (fun hz => Or.inr (h.2.2 (¬ z) hz))⟩

/-- With `ND_t`, a proposition possibly non-bottom and possibly deciding everything is so. -/
theorem decides_of_dia (nd : ∀ x y : Prop, x ≠ y → □ (x ≠ y)) (w : Prop) :
    ◇ (¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) →
      (¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) := fun hd =>
  ⟨ne_of_dia_ne w False (dia_mono _ _ (nec% (fun (h : ¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) => h.1)) hd),
   fun z => (dia_or _ _ (dia_forall_imp (λ z ↦ w ≤ z ∨ w ≤ ¬ z)
      (dia_mono _ _ (nec% (fun (h : ¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) => h.2)) hd) z)).elim
     (fun h => Or.inl (eq_of_dia_eq nd _ _ h)) (fun h => Or.inr (eq_of_dia_eq nd _ _ h))⟩

/-- `x ∧ Actuality` is `∃w. x ∧ (w ∧ ∀q. q → w ≤ q)`. -/
theorem and_actuality_eq (x : Prop) :
    (x ∧ ∃ w : Prop, w ∧ ∀ q, q → w ≤ q) = ∃ w : Prop, x ∧ (w ∧ ∀ q, q → w ≤ q) :=
  and_exists_distrib_eq _ x

/-- `c5-and-necessary-actuality-imply-atomicity` (at type `t` only)
(Proposition 2.6, right to left, through `□`Actuality): a non-bottom `x` is compatible
with Actuality; by `BF` some `w` is possibly true with `x` and an actual world; then
`w ≤ x` is possible, hence true by `ND`; and `w`, possibly non-bottom and deciding every
proposition, is so, by `ND`, hence an atom. -/
theorem c5_and_necessary_actuality_imply_atomicity_at_t :
    NecActuality → NecNecessityOfDistinctness Prop → Atomicity Prop := fun hna hnd x =>
  have nd : ∀ x y : Prop, x ≠ y → □ (x ≠ y) := box_elim hnd
  have bf := bf_of_box_nd_t (σ := Prop) hnd
  (em (x = False)).elim (fun h => Or.inl (le_neg_of_eq_false x h)) fun hx => Or.inr (by
    have h1 : ◇ (x ∧ Actuality) := dia_and_of_dia_box x Actuality hx hna
    have h2 : ◇ (∃ w : Prop, x ∧ (w ∧ ∀ q, q → w ≤ q)) := by
      rw [← and_actuality_eq]; exact h1
    obtain ⟨w, hw⟩ := dia_exists_of_bf bf _ h2
    exact ⟨w, atom_of_decides w (decides_of_dia nd w (dia_mono _ _ (nec% (decides_of_actual x w)) hw)),
      eq_of_dia_eq nd _ _ (dia_mono _ _ (nec% (le_of_actual_and x w)) hw)⟩)

/-- Boolean Completeness at `t → t` and `□ND_t` give Actuality, unfolded, for necessitation. -/
theorem actuality_of_bc_box_nd_t :
    BooleanCompleteness (Prop → Prop) → □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → Actuality :=
  c5_and_completeness_imply_actuality

/-- `necessary-boolean-completeness-r-and-necessary-distinctness-necessary-t-imply-necessary-actuality`:
Proposition 2.5 necessitated. -/
theorem necessary_boolean_completeness_r_and_necessary_distinctness_necessary_t_imply_necessary_actuality :
    NecBooleanCompleteness (Prop → Prop) → NecNecessityOfDistinctnessT → NecActuality := fun hnb hnd =>
  modal_K _ _ (modal_K _ _ (nec% actuality_of_bc_box_nd_t) hnb) (modal_four _ hnd)

/-- `c5-and-necessary-completeness-imply-atomicity` (at type `t` only)
(Proposition 2.6, right to left). -/
theorem c5_and_necessary_completeness_imply_atomicity_at_t :
    NecBooleanCompleteness (Prop → Prop) → NecNecessityOfDistinctness Prop → Atomicity Prop := fun hnb hnd =>
  c5_and_necessary_actuality_imply_atomicity_at_t
    (necessary_boolean_completeness_r_and_necessary_distinctness_necessary_t_imply_necessary_actuality hnb hnd) hnd

/-- Actuality and `□ND_t` give Rigid Comprehension at `σ → t`, unfolded, for necessitation. -/
theorem rc_of_actuality_box_nd_t {σ : Type} [Ty σ] :
    Actuality → □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → RigidComprehension (σ → Prop) :=
  c5_and_actuality_imply_rigid_comprehension

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension` (Classicism, §2.3: `C5` +
Atomicity = `C5` + `□`Rigid Comprehension), at `σ → t`, its list form being the map's
record, from Atomicity at `t`: `□`Actuality, and Proposition 2.10 necessitated. The
converse is `necessary_rigid_comprehension_r_implies_necessary_actuality` with the last
record. -/
theorem c5_and_atomicity_imply_necessary_rigid_comprehension
    {σ : Type} [Ty σ] :
    Atomicity Prop → NecNecessityOfDistinctness Prop → NecRigidComprehension (σ → Prop) := fun at_ hnd =>
  modal_K _ _ (modal_K _ _ (nec% (rc_of_actuality_box_nd_t (σ := σ)))
    (atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality at_ hnd))
    (modal_four _ hnd)

/-- `necessary-rigid-comprehension-r-and-necessary-distinctness-necessary-t-imply-atomicity-t`:
`□`Rigid Comprehension at `t → t` gives `□`Actuality (Proposition 2.9 necessitated), and
`C5` then gives Atomicity. -/
theorem necessary_rigid_comprehension_r_and_necessary_distinctness_necessary_t_imply_atomicity_t :
    NecRigidComprehension (Prop → Prop) → NecNecessityOfDistinctnessT → AtomicityT := fun hrc hnd =>
  c5_and_necessary_actuality_imply_atomicity_at_t
    (necessary_rigid_comprehension_r_implies_necessary_actuality hrc) hnd

/-! Rigid Comprehension and `BF` give `□BF` (Proposition 2.12, n. 43); Rigid Comprehension
and `ND` give Plenitude (Proposition 2.16, n. 49). -/

/-- Inside the box: weak inextensibility of `F` and `□∀x. Fx` give `BF`. -/
theorem bf_of_weaklyInextensible {σ : Type} [Ty σ] (F : σ → Prop) :
    WeaklyInextensible F → □ (∀ x, F x) → ∀ Y : σ → Prop, (∀ x, □ (Y x)) → □ (∀ x, Y x) :=
  fun hI hall Y hY =>
    modal_K _ _ (modal_K _ _ (nec% (forall_imp_forall F Y)) (hI Y (fun z _ => hY z))) hall

/-- `rigid-comprehension-and-bf-imply-necessary-bf` (Proposition 2.12): a
rigid `F` coextensive with self-identity holds necessarily of everything, so by `BF`
`□∀x. Fx`; its inextensibility, necessitated, then gives `BF` in every world. -/
theorem rigid_comprehension_and_bf_imply_necessary_bf {σ : Type} [Ty σ] :
    RigidComprehension (σ → Prop) → Barcan σ → NecBarcan σ := fun rc bf =>
  (rc (λ x ↦ x = x)).elim fun F hF =>
    have hall : □ (∀ x, F x) :=
      bf F (fun x => weaklyPersistent_apply (weaklyPersistent_of_persistent hF.1.1) x ((hF.2 x).1 rfl))
    modal_K _ _ (modal_K _ _ (nec% (bf_of_weaklyInextensible F)) hF.1.2) (modal_four _ hall)

/-- `Rs x Q → ∀z. (∀P. Rs x P → Pz) → Qz`. -/
theorem z_imp_of_rs₂ {σ σ' : Type} [Ty σ] [Ty σ'] (Rs : σ → (σ' → Prop) → Prop) (x : σ)
    (Q : σ' → Prop) : Rs x Q → ∀ z, (∀ P : σ' → Prop, Rs x P → P z) → Q z :=
  fun h z hz => hz Q h

/-- `∀y P. Rs y P → y ≠ x ∨ P = Q` gives `∀z. Qz → ∀P. Rs x P → Pz`. -/
theorem z_of_functional₂ {σ σ' : Type} [Ty σ] [Ty σ'] (Rs : σ → (σ' → Prop) → Prop) (x : σ)
    (Q : σ' → Prop) :
    (∀ y P, Rs y P → y ≠ x ∨ P = Q) → ∀ z, Q z → ∀ P : σ' → Prop, Rs x P → P z :=
  fun h z hQz P hP => (h x P hP).elim (fun hne => (hne rfl).elim) (fun e => e ▸ hQz)

/-- `weak-rigid-comprehension-and-nd-imply-plenitude` (Proposition 2.16, with Weak Rigid
Comprehension), for relations `σ → (σ' → t) → t`, its list form in `σ'` being the map's
record: with `Rs` weakly rigid and
coextensive with the functional `R`, `Z := λyz. ∀P. Rs y P → Pz` represents it. At `x`
with `RxQ`: `Rs x Q` is necessary, so `Zx ≤ Q`; and every `Rs y P` has `y ≠ x ∨ P = Q`,
necessarily so by `ND` and `NI`, so by weak inextensibility necessarily, which gives
`Q ≤ Zx`. Only weak persistence and weak inextensibility are used. -/
theorem weak_rigid_comprehension_and_nd_imply_plenitude {σ' σ : Type} [Ty σ'] [Ty σ] :
    WeakRigidComprehension (σ → (σ' → Prop) → Prop) → NecessityOfDistinctness σ →
      Plenitude σ (σ' → Prop) :=
  fun rc nd R hR => (rc R).elim fun Rs hRs =>
    ⟨λ y z ↦ ∀ P : σ' → Prop, Rs y P → P z, fun x => (hR x).elim fun Q hQ =>
      have hRsQ : Rs x Q := (hRs.2 x Q).1 hQ.1
      have hfun : ∀ y P, Rs y P → y ≠ x ∨ P = Q := fun y P hp =>
        (em (y = x)).elim (fun e => Or.inr (by
            rw [e] at hp
            exact (hQ.2 P ((hRs.2 x P).2 hp)).symm))
          Or.inl
      have hle1 : (λ z ↦ ∀ P : σ' → Prop, Rs x P → P z) ≤ Q := (le_iff _ _).2
        (modal_K _ _ (nec% (z_imp_of_rs₂ Rs x Q))
          (hRs.1.1 x Q hRsQ))
      have hle2 : Q ≤ (λ z ↦ ∀ P : σ' → Prop, Rs x P → P z) := (le_iff _ _).2
        (modal_K _ _ (nec% (z_of_functional₂ Rs x Q))
          (hRs.1.2 (λ y P ↦ y ≠ x ∨ P = Q)
            (fun y P hp => box_ne_or_eq nd y x P Q (hfun y P hp))))
      show R x (λ z ↦ ∀ P : σ' → Prop, Rs x P → P z) by
        rw [← le_antisymm_arrow Q _ hle2 hle1]; exact hQ.1⟩

/-! Proposition 2.11 (n. 42), reduced to a restriction principle.

The paper derives Rigid Comprehension from `□`Atomicity, Boolean Completeness and `BF`
with `X*`, the least upper bound of the haecceities of the `X`s. Parts (i) to (iii) of
n. 42 (`X*` is coextensive with `X`, given Actuality, and persistent) go through as
written. Part (iv), inextensibility, has two steps that do not: it boxes a pointwise
claim with `BF` where `□BF` would be needed, and its "without loss of generality" step
assumes that, for `w` an atom and `w′` possibly an atom below `X*z ∧ ¬Yz`, the greatest
lower bound `w″` of the `p` with `w ≤ (p = w′)` is still identical to `w′` wherever `w`
is true, which nothing in the premises gives (see `HANDOFF.md`, §4).

What part (iv) needs from `w″` is only this: for a proposition `p` (here `∀x. X*x →
□Yx`) and a proposition `q` (here `∃z. X*z ∧ ¬Yz`), a proposition `r` that is identical
to `q` wherever `p` is true (`p ≤ (r = q)`) and that entails everything `p` makes `q`
entail (`p ≤ (q ≤ s)` gives `r ≤ s`): `q` restricted to what is accessible from the
`p`-worlds. Given that, for every `p` and `q`, inextensibility follows with `BF` at the
type of properties only, and without atoms. The restriction principle holds in `C5`,
with `r := q ∧ ◇p` (`restriction_of_box_b`). `□`Atomicity, Boolean Completeness and `BF`
do not give it: Cian reports a countermodel to Proposition 2.11 (1 October). -/

/-- `Gu`, then `∀z. Gz → □Yz` makes `q ≤ Yu`. -/
theorem le_of_inext_premise {σ : Type} [Ty σ] (G Y : σ → Prop) (q : Prop) (u : σ) :
    G u → G ⊆ boxAt Y → q ≤ Y u :=
  fun hg hA => (le_iff_prop _ _).2 (box_imp_of_box q (Y u) (hA u hg))

/-- `r = ∃z. Gz ∧ ¬Yz` and `∀z. Gz → r → Yz` give `∀z. Gz → Yz`. -/
theorem forall_of_restricted {σ : Type} [Ty σ] (G Y : σ → Prop) (r : Prop) :
    r = (∃ z, G z ∧ ¬ Y z) → G ⊆ (λ z ↦ r → Y z) → G ⊆ Y :=
  fun e h z hg => (em (Y z)).elim id fun hn => h z hg (e ▸ ⟨z, hg, hn⟩)

/-- Inside the box: where `p` holds, `r = q`, so `□∀z. Gz → r → Yz` gives `□∀z. Gz → Yz`. -/
theorem box_forall_of_restricted {σ : Type} [Ty σ] (G Y : σ → Prop) (p r : Prop) :
    (p → r = (∃ z, G z ∧ ¬ Y z)) → □ (G ⊆ λ z ↦ r → Y z) → p → □ (G ⊆ Y) :=
  fun hrq hb hp => modal_K _ _ (modal_K _ _ (nec% (forall_of_restricted G Y r))
    (necessity_of_identity r _ (hrq hp))) hb

/-- **Proposition 2.11, reduced** (n. 42, with part (iv) repaired): Actuality, Boolean
Completeness at `σ → t`, `BF` at the type of properties, and the restriction principle
give Rigid Comprehension at `σ → t`. The witness is `X*`, the least upper bound of the
haecceities of the `X`s. For inextensibility, fix `Y`; with `p := ∀z. X*z → □Yz` and
`q := ∃z. X*z ∧ ¬Yz`, restriction gives `r`; each `X`-thing `u` has `□X*u`, so
`p ≤ (q ≤ Yu)`, so `r ≤ Yu`, so `λx. r → Yx` is above `X*`; and where `p` holds `r = q`,
so `X* ≤ Y` there. `BF` at `σ → t` boxes the quantifier over `Y`. -/
theorem rigid_comprehension_r_of_restriction {σ : Type} [Ty σ] (act : Actuality)
    (bc : BooleanCompleteness (σ → Prop)) (bf : Barcan (σ → Prop))
    (res : ∀ p q : Prop, ∃ r : Prop, p ≤ (r = q) ∧ ∀ s : Prop, p ≤ (q ≤ s) → r ≤ s) :
    RigidComprehension (σ → Prop) := fun X =>
  (bc (λ Y ↦ UB Y (λ Z ↦ ∃ u, X u ∧ Z = λ x ↦ u = x))).elim fun G hG =>
    have hbox : X ⊆ boxAt G := box_lub_haec_of X G hG
    have hpers : Persistent G :=
      (le_iff G (boxAt G)).1 (lub_haec_le X G hG _ fun u hu => modal_four _ (hbox u hu))
    have hinext : Inextensible G :=
      bf (λ Y ↦ G ⊆ boxAt Y → □ (G ⊆ Y)) fun Y =>
        (res (G ⊆ boxAt Y) (∃ z, G z ∧ ¬ Y z)).elim fun r hr =>
          have hGr : G ≤ (λ x ↦ r → Y x) := lub_haec_le X G hG _ fun u hu =>
            (le_iff_prop _ _).1 (hr.2 (Y u) ((le_iff_prop _ _).2
              (modal_K _ _ (nec% (le_of_inext_premise G Y (∃ z, G z ∧ ¬ Y z) u)) (hbox u hu))))
          modal_K _ _ (modal_K _ _ (nec% (box_forall_of_restricted G Y (G ⊆ boxAt Y) r))
            ((le_iff_prop _ _).1 hr.1)) (modal_four _ ((le_iff G _).1 hGr))
    ⟨G, ⟨hpers, hinext⟩, fun u =>
      ⟨fun hu => box_elim (hbox u hu), lub_haec_imp act X G hG u⟩⟩

/-- `(∀p. p → □◇p) → p → (q ∧ ◇p) = q`. -/
theorem and_dia_eq_of_b (p q : Prop) : (∀ p : Prop, p → □ ◇ p) → p → (q ∧ ◇ p) = q :=
  fun b hp => by rw [b p hp]; exact and_true_eq q

/-- `q ≤ s` gives `□(q → s)`, unfolded. -/
theorem box_imp_of_le' (q s : Prop) : q ≤ s → □ (q → s) := fun h => (le_iff_prop q s).1 h

/-- With `B`: `□(p → q ≤ s)`, `q` and `◇p` give `s`. -/
theorem le_of_and_dia_of_b (p q s : Prop) :
    (∀ p : Prop, p → □ ◇ p) → □ (p → q ≤ s) → q ∧ ◇ p → s := fun b h hq =>
  b_dia_box_imp b (q → s) (dia_mono _ _ (nec% (box_imp_of_le' q s)) (dia_mono _ _ h hq.2)) hq.1

/-- The restriction principle holds in `C5`, with `r := q ∧ ◇p`. -/
theorem restriction_of_box_b (hb : □ (∀ p : Prop, p → □ ◇ p)) :
    ∀ p q : Prop, ∃ r : Prop, p ≤ (r = q) ∧ ∀ s : Prop, p ≤ (q ≤ s) → r ≤ s :=
  fun p q => ⟨q ∧ ◇ p,
    (le_iff_prop _ _).2 (modal_K _ _ (nec% (and_dia_eq_of_b p q)) hb),
    fun s h => (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (le_of_and_dia_of_b p q s)) hb)
      (modal_four _ ((le_iff_prop _ _).1 h)))⟩


/-! ### Rigid Power in `C5` (3 October 2026) -/

/-- Being rigid and entailing `F` is necessary if true: each conjunct is boxed, persistence
and inextensibility by definition and `X ≤ F` as `□(X ⊑ F)`, and `4` boxes them again. -/
theorem rigid_and_le_box {σ : Type} [Ty σ] (F X : σ → Prop) :
    (Rigid X ∧ X ≤ F) → □ (Rigid X ∧ X ≤ F) := fun ⟨⟨hp, hi⟩, hle⟩ => by
  have h3 : □ (X ≤ F) := modal_K _ _ (nec% (fun h : □ (X ⊆ F) => le_of_box_incl h))
    (modal_four _ ((le_iff X F).1 hle))
  show □ ((Persistent X ∧ Inextensible X) ∧ X ≤ F)
  rw [box_and_eq, box_and_eq]
  exact ⟨⟨modal_four _ hp, modal_four _ hi⟩, h3⟩

/-- Rigid Power at `σ → t` in `C5`: the power property `λX. Rigid(X) ∧ X ≤ F` is persistent,
by the last lemma, and in `C5` a persistent property is inextensible (n. 41). `F` need not
be rigid. -/
theorem c5_implies_rigid_power {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → RigidPower (σ → Prop) := fun hnd F _ =>
  have hP : Persistent (fun X : σ → Prop => Rigid X ∧ X ≤ F) :=
    nec% (fun X h => rigid_and_le_box F X h)
  ⟨hP, inextensible_of_persistent_c5 (σ := σ → Prop) hnd _ hP⟩

/-- `c5-implies-necessary-rigid-power`: the last theorem necessitated, with `4`. -/
theorem c5_implies_necessary_rigid_power {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → NecRigidPower (σ → Prop) := fun hnd =>
  modal_K _ _ (nec% (c5_implies_rigid_power (σ := σ))) (modal_four _ hnd)


/-- `c5-implies-tame-rigidity`, at `σ → t`: a weakly rigid property is persistent
(`persistent_of_weaklyRigid`), and in `C5` a persistent property is inextensible (n. 41). -/
theorem c5_implies_tame_rigidity {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → TameRigidity (σ → Prop) := fun hnd F hF =>
  ⟨persistent_of_weaklyRigid hF, inextensible_of_persistent_c5 hnd F (persistent_of_weaklyRigid hF)⟩

/-- `c5-implies-necessary-tame-rigidity`: the last theorem necessitated, with `4`. -/
theorem c5_implies_necessary_tame_rigidity {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → NecTameRigidity (σ → Prop) := fun hnd =>
  modal_K _ _ (nec% (c5_implies_tame_rigidity (σ := σ))) (modal_four _ hnd)

end Classicism.Proofs
