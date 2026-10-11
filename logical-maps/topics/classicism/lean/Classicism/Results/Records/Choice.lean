import Classicism.Paper
import Classicism.Principles

/-!
# Proofs of map records: Choice, Plenitude and Transversals

Records concluding in the principles of the map's category `choice` (Classicism, §2.4;
Propositions 2.13 and 2.15), Transversals and Modalized Plenitude.
The conventions are in `Results/Records.lean`.
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-! ### Choice (Classicism, §2.4) -/

/-- `functional-choice-r-implies-relational-choice-r`. Functional Choice cannot be
applied directly, because the output type may be `e` while an operation's output type may
not. Replace each output `y` by its haecceity `λw. w = y`, of the admitted type `τt`, and
choose among haecceities instead: the relation `λx H. ∃y. H = (λw. w = y) ∧ (Ux)y` is
serial because `U` is, so Functional Choice supplies `X : σ → τ → Prop` with `X x` a
haecceity of some `U`-successor of `x`. That `X` is itself the required subrelation, since
haecceities are injective by identity elimination. The record's argument treats the `e`
case separately; the haecceity detour is uniform, so no case split is needed. The instance
of Functional Choice used is the one at `σ`, `τ → t`, for Relational Choice at `σ`, `τ`. -/
theorem functional_choice_r_implies_relational_choice_r {σ τ : Type} [Ty σ] [Ty τ] :
    FunctionalChoice σ (τ → Prop) → RelationalChoice σ τ := by
  intro fc U hser
  -- The relation between an argument and the haecceities of its `U`-successors.
  have hser' : Serial (λ (x : σ) (H : τ → Prop) ↦ ∃ y, H = (λ w ↦ w = y) ∧ U x y) := by
    intro x
    obtain ⟨y, hy⟩ := hser x
    exact ⟨λ w ↦ w = y, y, rfl, hy⟩
  obtain ⟨X, hX⟩ := fc _ hser'
  refine ⟨X, ?_, ?_⟩
  · -- `X x` is the haecceity of one `U`-successor, so it holds of exactly that one.
    intro x
    obtain ⟨y, hXy, hUy⟩ := hX x
    refine ⟨y, ?_, ?_⟩
    · show X x y
      rw [hXy]
    · intro z hz
      rw [hXy] at hz
      exact hz.symm
  · -- And everything it holds of is that successor, so it is a subrelation of `U`.
    intro x y hxy
    obtain ⟨w, hXw, hUw⟩ := hX x
    rw [hXw] at hxy
    rw [hxy]
    exact hUw

/-! Plenitude (Classicism, §2.4, Propositions 2.13 and 2.15) -/

/-- The relation mapping each truth to itself and each falsehood to `⊤` is functional
(stated unfolded, so that the audits do not read it as a record). -/
theorem actual_rel_functional :
    ∀ p : Prop, ∃ q : Prop, ((p ∧ p = q) ∨ (¬ p ∧ q = True)) ∧
      ∀ z : Prop, ((p ∧ p = z) ∨ (¬ p ∧ z = True)) → q = z :=
  fun p => (em p).elim
    (fun hp => ⟨p, Or.inl ⟨hp, rfl⟩, fun z hz => hz.elim (fun h => h.2) (fun h => absurd hp h.1)⟩)
    (fun hp => ⟨True, Or.inr ⟨hp, rfl⟩, fun z hz => hz.elim (fun h => absurd h.1 hp) (fun h => h.2.symm)⟩)

/-- `∀p. Zp` gives `Zq`. -/
theorem all_imp (Z : Prop → Prop) (q : Prop) : (∀ p, Z p) → Z q := fun h => h q

/-- `plenitude-r-implies-actuality` (Proposition 2.15): Plenitude represents that relation
by an operation `Z`, with `Zp = p` for true `p` and `Zp = ⊤` for false `p`. Then `∀p. Zp`
is true, and it entails each `Zq`, hence each truth `q`. -/
theorem plenitude_r_implies_actuality : Plenitude Prop Prop → Actuality := fun pl =>
  (pl _ actual_rel_functional).elim fun Z hZ =>
    ⟨∀ p, Z p,
     fun p => (hZ p).elim (fun h => h.2 ▸ h.1) (fun h => h.2 ▸ trivial),
     fun q hq => (hZ q).elim
       (fun h => h.2 ▸ le_of_box_incl (nec% (all_imp Z q)))
       (fun h => absurd hq h.1)⟩

/-- The relation mapping `x` to `⊤` and everything else to `⊥` is functional. -/
theorem haec_rel_functional {σ : Type} [Ty σ] (x : σ) :
    Functional (λ z (w : Prop) ↦ (x = z ∧ w = True) ∨ (x ≠ z ∧ w = False)) := fun z =>
  (em (x = z)).elim
    (fun h => ⟨True, Or.inl ⟨h, rfl⟩, fun w hw => hw.elim (fun h' => h'.2.symm) (fun h' => absurd h h'.1)⟩)
    (fun h => ⟨False, Or.inr ⟨h, rfl⟩, fun w hw => hw.elim (fun h' => absurd h'.1 h) (fun h' => h'.2.symm)⟩)

/-- `Zx = ⊤` and `Zy = ⊥` make `x ≠ y`. -/
theorem ne_of_values {σ : Type} [Ty σ] (Z : σ → Prop) (x y : σ) : Z x = True → Z y = False → x ≠ y := by
  intro hx hy hxy
  rw [hxy] at hx
  rw [hx] at hy
  exact hy ▸ trivial

/-- `plenitude-r-implies-distinctness-necessary-r` (Proposition 2.13): for `x ≠ y`, the
operation representing "`⊤` at `x`, `⊥` elsewhere" has `Zx = ⊤` and `Zy = ⊥`, both
necessarily, so necessarily `x ≠ y`. -/
theorem plenitude_r_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    Plenitude σ Prop → NecessityOfDistinctness σ := fun pl x y hxy =>
  (pl _ (haec_rel_functional x)).elim fun Z hZ =>
    have hx : Z x = True := (hZ x).elim (fun h => h.2) (fun h => absurd rfl h.1)
    have hy : Z y = False := (hZ y).elim (fun h => absurd h.1 hxy) (fun h => h.2)
    modal_K _ _ (modal_K _ _ (nec% (ne_of_values Z x y)) (necessity_of_identity _ _ hx))
      (necessity_of_identity _ _ hy)

/-- `necessary-plenitude-r-implies-plenitude-r`: `T`. -/
theorem necessary_plenitude_r_implies_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecPlenitude σ τ → Plenitude σ τ := box_elim

/-- `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`: Proposition 2.13
necessitated. -/
theorem necessary_plenitude_r_implies_necessary_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecPlenitude σ Prop → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (plenitude_r_implies_distinctness_necessary_r (σ := σ)))

/-- `necessary-plenitude-r-implies-necessary-actuality`: Proposition 2.15 necessitated. -/
theorem necessary_plenitude_r_implies_necessary_actuality :
    NecPlenitude Prop Prop → NecActuality :=
  modal_K _ _ (nec% plenitude_r_implies_actuality)

/-- `functional-choice-r-implies-plenitude-r`: a functional relation is serial. -/
theorem functional_choice_r_implies_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    FunctionalChoice σ τ → Plenitude σ τ :=
  fun fc U hU => fc U (fun x => (hU x).elim fun y hy => ⟨y, hy.1⟩)

/-- `necessary-functional-choice-r-implies-functional-choice-r`: `T`. -/
theorem necessary_functional_choice_r_implies_functional_choice_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecFunctionalChoice σ τ → FunctionalChoice σ τ := box_elim
/-- `necessary-relational-choice-r-implies-relational-choice-r`: `T`. -/
theorem necessary_relational_choice_r_implies_relational_choice_r {σ τ : Type} [Ty σ] [Ty τ] :
    NecRelationalChoice σ τ → RelationalChoice σ τ := box_elim
/-- `necessary-functional-choice-r-implies-necessary-plenitude-r`. -/
theorem necessary_functional_choice_r_implies_necessary_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecFunctionalChoice σ τ → NecPlenitude σ τ :=
  modal_K _ _ (nec% (functional_choice_r_implies_plenitude_r (σ := σ) (τ := τ)))
/-- `necessary-functional-choice-r-implies-necessary-relational-choice-r`. -/
theorem necessary_functional_choice_r_implies_necessary_relational_choice_r {σ τ : Type} [Ty σ]
    [Ty τ] : NecFunctionalChoice σ (τ → Prop) → NecRelationalChoice σ τ :=
  modal_K _ _ (nec% (functional_choice_r_implies_relational_choice_r (σ := σ) (τ := τ)))
/-- `relational-choice-and-plenitude-imply-functional-choice-r`: Relational Choice selects
a functional subrelation, and Plenitude represents it by an operation. -/
theorem relational_choice_and_plenitude_imply_functional_choice_r {σ τ : Type} [Ty σ] [Rel τ] :
    RelationalChoice σ τ → Plenitude σ τ → FunctionalChoice σ τ := fun rc pl U hser =>
  (rc U hser).elim fun S hS => (pl S hS.1).elim fun X hX => ⟨X, fun x => hS.2 x (X x) (hX x)⟩
/-- `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice`. -/
theorem necessary_relational_choice_and_necessary_plenitude_imply_necessary_functional_choice
    {σ τ : Type} [Ty σ] [Rel τ] :
    NecRelationalChoice σ τ → NecPlenitude σ τ → NecFunctionalChoice σ τ := fun h₁ h₂ =>
  modal_K _ _ (modal_K _ _
    (nec% (relational_choice_and_plenitude_imply_functional_choice_r (σ := σ) (τ := τ))) h₁) h₂

/-! ### Transversals (25–28 September) -/

/-- `(w → ∀z. Y'z ↔ Xz ∧ w) → (∀z. Y'z → w) → ∀z. Y'z ↔ Xz ∧ w`. -/
theorem coext_of_actual_imp {σ : Type} [Ty σ] (X Y' : σ → Prop) (w : Prop) :
    (w → ∀ z, Y' z ↔ (X z ∧ w)) → (∀ z, Y' z → w) → ∀ z, Y' z ↔ (X z ∧ w) :=
  fun h hY z => ⟨fun hy => (h (hY z hy) z).1 hy, fun hx => (h hx.2 z).2 hx⟩

/-- `actuality-implies-transversal`: with `w` the actual world, the properties that can be
instantiated only if `w` obtains form a transversal; `λz. Xz ∧ w` is the one coextensive
with `X`, and two such that are coextensive are necessarily so, so identical. -/
theorem actuality_implies_transversal {σ : Type} [Ty σ] : Actuality → Transversal σ := fun act =>
  act.elim fun w hw =>
    ⟨λ Y ↦ □ (∀ z, Y z → w), fun X =>
      ⟨λ z ↦ X z ∧ w, nec% (fun (z : σ) (h : X z ∧ w) => h.2),
        fun z => ⟨fun hx => ⟨hx, hw.1⟩, fun h => h.1⟩,
        fun Y' hY' => intensionality Y' _ (modal_K _ _ (modal_K _ _
          (nec% (coext_of_actual_imp X Y' w))
          ((le_iff_prop _ _).1 (hw.2 _ fun z =>
            ⟨fun hy => ⟨(hY'.2 z).2 hy, hw.1⟩, fun hx => (hY'.2 z).1 hx.1⟩))) hY'.1)⟩⟩

/-- `necessary-actuality-implies-necessary-transversal`: necessitated, and `K`. -/
theorem necessary_actuality_implies_necessary_transversal {σ : Type} [Ty σ] :
    NecActuality → NecTransversal σ :=
  modal_K _ _ (nec% (actuality_implies_transversal (σ := σ)))

/-- `necessary-transversal-r-implies-transversal-r`: `T`. -/
theorem necessary_transversal_r_implies_transversal_r {σ : Type} [Ty σ] :
    NecTransversal σ → Transversal σ := fun h => box_elim h

/-- `transversal-choice-r-implies-transversal-r`: coextensiveness is an equivalence
relation on properties, and a transversal of it is a transversal. -/
theorem transversal_choice_r_implies_transversal_r {σ : Type} [Ty σ] :
    TransversalChoice (σ → Prop) → Transversal σ := fun tc =>
  (tc (λ X Y ↦ ∀ z, X z ↔ Y z)
      ⟨fun _ _ => Iff.rfl, fun _ _ h z => (h z).symm,
        fun _ _ _ h₁ h₂ z => ⟨fun h => (h₂ z).1 ((h₁ z).1 h), fun h => (h₁ z).2 ((h₂ z).2 h)⟩⟩).elim
    fun F hF => ⟨F, fun X => (hF X).elim fun Y hY =>
      ⟨Y, hY.2.1, hY.1, fun Y' hY' => (hY.2.2 Y' ⟨hY'.2, hY'.1⟩).symm⟩⟩

/-- `necessary-transversal-choice-r-implies-necessary-transversal-r`: necessitated, and `K`. -/
theorem necessary_transversal_choice_r_implies_necessary_transversal_r {σ : Type} [Ty σ] :
    NecTransversalChoice (σ → Prop) → NecTransversal σ :=
  modal_K _ _ (nec% (transversal_choice_r_implies_transversal_r (σ := σ)))

/-- `necessary-transversal-choice-r-implies-transversal-choice-r`: `T`. -/
theorem necessary_transversal_choice_r_implies_transversal_choice_r {σ : Type} [Ty σ] :
    NecTransversalChoice σ → TransversalChoice σ := fun h => box_elim h

/-- With an element `x₀`, `(UC)y := Cy ∨ ¬∃z. Cz` is serial. -/
theorem serial_cell {σ : Type} [Ty σ] (x₀ : σ) :
    ∀ C : σ → Prop, ∃ y, C y ∨ ¬ ∃ z, C z := fun C =>
  (em (∃ z, C z)).elim (fun h => h.elim fun z hz => ⟨z, Or.inl hz⟩) (fun h => ⟨x₀, Or.inr h⟩)

/-- `transversal-and-relational-choice-imply-transversal-choice`: Relational Choice picks
an element `y` from each nonempty property `C`, functionally in `C`; the transversal of
`R` holds of the element picked from the Transversal's representative of a cell. Where
`σ` is empty there is nothing to pick. -/
theorem transversal_and_relational_choice_imply_transversal_choice {σ : Type} [Ty σ] :
    Transversal σ → RelationalChoice (σ → Prop) σ → TransversalChoice σ := by
  intro tr rc R hR
  refine (em (∃ x₀ : σ, x₀ = x₀)).elim (fun hx₀ => ?_)
    (fun hn => ⟨λ _ ↦ True, fun x => (hn ⟨x, rfl⟩).elim⟩)
  obtain ⟨x₀, -⟩ := hx₀
  obtain ⟨F, hF⟩ := tr
  obtain ⟨S, hSf, hSU⟩ := rc (λ C y ↦ C y ∨ ¬ ∃ z, C z) (serial_cell x₀)
  refine ⟨λ y ↦ ∃ Y : σ → Prop, F Y ∧ (∀ z, Y z ↔ R y z) ∧ S Y y, fun x => ?_⟩
  obtain ⟨Yx, hFYx, hcoYx, huYx⟩ := hF (R x)
  obtain ⟨y, hSy, hSu⟩ := hSf Yx
  have hYy : Yx y := (hSU Yx y hSy).elim id (fun h => (h ⟨x, (hcoYx x).1 (hR.1 x)⟩).elim)
  have hRxy : R x y := (hcoYx y).2 hYy
  refine ⟨y, hRxy, ⟨Yx, hFYx, fun z => ⟨fun hz => hR.2.2 y x z (hR.2.1 x y hRxy) ((hcoYx z).2 hz),
    fun hz => (hcoYx z).1 (hR.2.2 x y z hRxy hz)⟩, hSy⟩, ?_⟩
  rintro z ⟨hRxz, Y', hFY', hcoY', hSY'⟩
  have e : Y' = Yx := huYx Y' ⟨hFY', fun u =>
    ⟨fun hu => (hcoY' u).2 (hR.2.2 z x u (hR.2.1 x z hRxz) hu),
     fun hu => hR.2.2 x z u hRxz ((hcoY' u).1 hu)⟩⟩
  rw [e] at hSY'
  exact hSu z hSY'

/-- `relational-choice-and-extensionality-imply-transversal-choice`: as above, the element
picked from a cell; Extensionality makes coextensive cells identical. -/
theorem relational_choice_and_extensionality_imply_transversal_choice {σ : Type} [Ty σ] :
    RelationalChoice (σ → Prop) σ → Extensionality (σ → Prop) → TransversalChoice σ := by
  intro rc ext R hR
  refine (em (∃ x₀ : σ, x₀ = x₀)).elim (fun hx₀ => ?_)
    (fun hn => ⟨λ _ ↦ True, fun x => (hn ⟨x, rfl⟩).elim⟩)
  obtain ⟨x₀, -⟩ := hx₀
  obtain ⟨S, hSf, hSU⟩ := rc (λ C y ↦ C y ∨ ¬ ∃ z, C z) (serial_cell x₀)
  have hcell : ∀ x y, S (R x) y → R x y := fun x y h =>
    (hSU (R x) y h).elim id (fun hn => (hn ⟨x, hR.1 x⟩).elim)
  refine ⟨λ y ↦ ∃ x, S (R x) y, fun x => ?_⟩
  obtain ⟨y, hSy, hSu⟩ := hSf (R x)
  refine ⟨y, hcell x y hSy, ⟨x, hSy⟩, ?_⟩
  rintro z ⟨hRxz, x₂, hS₂⟩
  have hR₂ : R x₂ z := hcell x₂ z hS₂
  have e : R x₂ = R x := ext (R x₂) (R x) fun u =>
    ⟨fun hu => hR.2.2 x z u hRxz (hR.2.2 z x₂ u (hR.2.1 x₂ z hR₂) hu),
     fun hu => hR.2.2 x₂ z u hR₂ (hR.2.2 z x u (hR.2.1 x z hRxz) hu)⟩
  rw [e] at hS₂
  exact hSu z hS₂

/-- Two coextensive weakly rigid properties are identical: each is below the other by
weak persistence and weak inextensibility, and Intensionality. -/
theorem eq_of_weaklyRigid {σ : Type} [Ty σ] (C C' : σ → Prop) (hC : WeaklyRigid C)
    (hC' : WeaklyRigid C') (hco : ∀ z, C z ↔ C' z) : C = C' :=
  le_antisymm_arrow C C'
    ((le_iff _ _).2 (hC.2 C' fun z hz => weaklyPersistent_apply hC'.1 z ((hco z).1 hz)))
    ((le_iff _ _).2 (hC'.2 C fun z hz => weaklyPersistent_apply hC.1 z ((hco z).2 hz)))

/-- `relational-choice-and-weak-rigid-comprehension-imply-transversal-choice`: as above,
with each cell represented by a weakly rigid coextension, which is unique. -/
theorem relational_choice_and_weak_rigid_comprehension_imply_transversal_choice
    {σ : Type} [Ty σ] :
    RelationalChoice (σ → Prop) σ → WeakRigidComprehension (σ → Prop) →
      TransversalChoice σ := by
  intro rc vw R hR
  refine (em (∃ x₀ : σ, x₀ = x₀)).elim (fun hx₀ => ?_)
    (fun hn => ⟨λ _ ↦ True, fun x => (hn ⟨x, rfl⟩).elim⟩)
  obtain ⟨x₀, -⟩ := hx₀
  obtain ⟨S, hSf, hSU⟩ := rc (λ C y ↦ C y ∨ ¬ ∃ z, C z) (serial_cell x₀)
  refine ⟨λ y ↦ ∃ C : σ → Prop, WeaklyRigid C ∧ (∀ z, C z ↔ R y z) ∧ S C y, fun x => ?_⟩
  obtain ⟨C, hC, hco⟩ := vw (R x)
  obtain ⟨y, hSy, hSu⟩ := hSf C
  have hCy : C y := (hSU C y hSy).elim id (fun hn => (hn ⟨x, (hco x).1 (hR.1 x)⟩).elim)
  have hRxy : R x y := (hco y).2 hCy
  refine ⟨y, hRxy, ⟨C, hC, fun z => ⟨fun hz => hR.2.2 y x z (hR.2.1 x y hRxy) ((hco z).2 hz),
    fun hz => (hco z).1 (hR.2.2 x y z hRxy hz)⟩, hSy⟩, ?_⟩
  rintro z ⟨hRxz, C', hC', hco', hSC'⟩
  have e : C' = C := eq_of_weaklyRigid C' C hC' hC fun u =>
    ⟨fun hu => (hco u).1 (hR.2.2 x z u hRxz ((hco' u).1 hu)),
     fun hu => (hco' u).2 (hR.2.2 z x u (hR.2.1 x z hRxz) ((hco u).2 hu))⟩
  rw [e] at hSC'
  exact hSu z hSC'

/-- `necessary-transversal-and-necessary-relational-choice-imply-necessary-transversal-choice`:
the unboxed record necessitated, and `K`. -/
theorem necessary_transversal_and_necessary_relational_choice_imply_necessary_transversal_choice
    {σ : Type} [Ty σ] :
    NecTransversal σ → NecRelationalChoice (σ → Prop) σ → NecTransversalChoice σ :=
  fun h₁ h₂ => modal_K _ _ (modal_K _ _
    (nec% (transversal_and_relational_choice_imply_transversal_choice (σ := σ))) h₁) h₂

/-- Rigid pairs are injective: `λuv. u = x ∧ v = y` determines `x` and `y`. -/
theorem pair_injective {σ τ : Type} [Ty σ] [Ty τ] (x x' : σ) (y y' : τ)
    (h : (λ (u : σ) (v : τ) ↦ u = x ∧ v = y) = (λ u v ↦ u = x' ∧ v = y')) :
    x = x' ∧ y = y' :=
  (congrFun (congrFun h x) y).mp ⟨rfl, rfl⟩

/-- `transversal-choice-r-implies-relational-choice-r`: code `x`, `y` as the rigid pair
`λuv. u = x ∧ v = y`. Relating two `U`-pairs with the same first coordinate, and any two
non-`U`-pairs, is an equivalence relation, by injectivity; a transversal of it picks one
`U`-pair for each `x`, and `(Sx)y := (Ux)y ∧ F⟨x, y⟩` is a functional subrelation of `U`. -/
theorem transversal_choice_r_implies_relational_choice_r {σ τ : Type} [Ty σ] [Ty τ] :
    TransversalChoice (σ → τ → Prop) → RelationalChoice σ τ := by
  intro tc U hU
  have hE : EquivRel (λ (P Q : σ → τ → Prop) ↦
      (∃ x, (∃ y, U x y ∧ P = (λ u v ↦ u = x ∧ v = y)) ∧
        (∃ y, U x y ∧ Q = (λ u v ↦ u = x ∧ v = y))) ∨
      ((¬ ∃ x y, U x y ∧ P = (λ u v ↦ u = x ∧ v = y)) ∧
        (¬ ∃ x y, U x y ∧ Q = (λ u v ↦ u = x ∧ v = y)))) :=
    ⟨fun P => (em (∃ x y, U x y ∧ P = (λ u v ↦ u = x ∧ v = y))).elim
        (fun h => h.elim fun x hx => hx.elim fun y hy => Or.inl ⟨x, ⟨y, hy⟩, ⟨y, hy⟩⟩)
        (fun h => Or.inr ⟨h, h⟩),
     fun _ _ h => h.elim (fun h => h.elim fun x hx => Or.inl ⟨x, hx.2, hx.1⟩)
        (fun h => Or.inr ⟨h.2, h.1⟩),
     fun _ _ _ h₁ h₂ => h₁.elim
      (fun h₁ => h₁.elim fun x hx => h₂.elim
        (fun h₂ => h₂.elim fun x' hx' =>
          hx.2.elim fun y hy => hx'.1.elim fun y' hy' =>
            have e : x = x' := (pair_injective x x' y y' (hy.2.symm.trans hy'.2)).1
            Or.inl ⟨x, hx.1, e ▸ hx'.2⟩)
        (fun h₂ => (h₂.1 (hx.2.elim fun y hy => ⟨x, y, hy⟩)).elim))
      (fun h₁ => h₂.elim
        (fun h₂ => (h₁.2 (h₂.elim fun x' hx' => hx'.1.elim fun y' hy' => ⟨x', y', hy'⟩)).elim)
        (fun h₂ => Or.inr ⟨h₁.1, h₂.2⟩))⟩
  obtain ⟨F, hF⟩ := tc _ hE
  refine ⟨λ x y ↦ U x y ∧ F (λ u v ↦ u = x ∧ v = y), fun x => ?_, fun _ _ h => h.1⟩
  obtain ⟨y₀, hy₀⟩ := hU x
  obtain ⟨P', hEP', hFP', hu⟩ := hF (λ u v ↦ u = x ∧ v = y₀)
  rcases hEP' with ⟨x₁, ⟨y₁, -, e₁⟩, ⟨y₂, hU₂, e₂⟩⟩ | ⟨hn, -⟩
  · have ex : x = x₁ := (pair_injective x x₁ y₀ y₁ e₁).1
    subst ex
    refine ⟨y₂, ⟨hU₂, e₂ ▸ hFP'⟩, fun z hz => ?_⟩
    have e₃ := hu (λ u v ↦ u = x ∧ v = z) ⟨Or.inl ⟨x, ⟨y₀, hy₀, rfl⟩, ⟨z, hz.1, rfl⟩⟩, hz.2⟩
    exact (pair_injective x x y₂ z (e₂.symm.trans e₃)).2
  · exact (hn ⟨x, y₀, hy₀, rfl⟩).elim

/-- `necessary-transversal-choice-r-implies-necessary-relational-choice-r`: the unboxed
record necessitated, and `K`. -/
theorem necessary_transversal_choice_r_implies_necessary_relational_choice_r
    {σ τ : Type} [Ty σ] [Ty τ] :
    NecTransversalChoice (σ → τ → Prop) → NecRelationalChoice σ τ :=
  modal_K _ _ (nec% (transversal_choice_r_implies_relational_choice_r (σ := σ) (τ := τ)))

/-! ### Modalized Plenitude (28 September)

At output `σ' → t`, its list form in `σ'` being the record at every output type: the
operation `Fx := λu. ∀y. Uxy → yu` represents `U` wherever its values are necessarily
unique, by Intensionality. -/

/-- `φ(x, y₀) → ∀u. y₀u ↔ Fxu`. -/
theorem mp_value_coext {σ σ' : Type} [Ty σ] [Ty σ'] (U : σ → (σ' → Prop) → Prop) (x : σ)
    (y₀ : σ' → Prop) :
    (U x y₀ ∧ ∀ z, U x z → y₀ = z) → ∀ u, y₀ u ↔ ∀ y : σ' → Prop, U x y → y u :=
  fun h u => ⟨fun hu y hy => (h.2 y hy) ▸ hu, fun hF => hF y₀ h.1⟩

/-- `□φ(x, y₀)` makes `y₀` the value `Fx`. -/
theorem mp_value {σ σ' : Type} [Ty σ] [Ty σ'] (U : σ → (σ' → Prop) → Prop) (x : σ)
    (y₀ : σ' → Prop) (h : □ (U x y₀ ∧ ∀ z, U x z → y₀ = z)) :
    y₀ = λ u ↦ ∀ y : σ' → Prop, U x y → y u :=
  intensionality _ _ (modal_K _ _ (nec% (mp_value_coext U x y₀)) h)

/-- `(∀x. ∃y. □φ(x, y)) → ∀x y. Uxy ↔ y = Fx`. -/
theorem mp_represents {σ σ' : Type} [Ty σ] [Ty σ'] (U : σ → (σ' → Prop) → Prop) :
    (∀ x, ∃ y, □ (U x y ∧ ∀ z, U x z → y = z)) →
      ∀ x (y : σ' → Prop), U x y ↔ y = λ u ↦ ∀ y' : σ' → Prop, U x y' → y' u :=
  fun H x y => (H x).elim fun y₀ hy₀ =>
    have e := mp_value U x y₀ hy₀
    have hφ := box_elim hy₀
    ⟨fun hU => (hφ.2 y hU).symm.trans e, fun hy => (hy.trans e.symm) ▸ hφ.1⟩

/-- `classicism-implies-modalized-plenitude-r`, at output `σ' → t`, its list form in `σ'`
being the map's record: `λxu. ∀y. Uxy → yu` necessarily represents `U`. -/
theorem classicism_implies_modalized_plenitude_r {σ' σ : Type} [Ty σ'] [Ty σ] :
    ModalizedPlenitude σ (σ' → Prop) := fun U hH =>
  ⟨λ x u ↦ ∀ y : σ' → Prop, U x y → y u, modal_K _ _ (nec% (mp_represents U)) hH⟩


/-- `necessary-intensional-choice-r-implies-intensional-choice-r`: `T`. -/
theorem necessary_intensional_choice_r_implies_intensional_choice_r {σ : Type} [Ty σ] :
    NecIntensionalChoice σ → IntensionalChoice σ := box_elim


/-- `extensionality-r-implies-intensional-choice-r`: Extensionality at `t` makes every truth
necessary. A necessarily instantiated `F` is instantiated, by `a` say, so `□Fa`; then
`λx. x = a` entails `F` and is necessarily uniquely instantiated. -/
theorem extensionality_r_implies_intensional_choice_r {σ : Type} [Ty σ] :
    Extensionality Prop → IntensionalChoice σ := fun ext F hF =>
  (box_elim hF).elim fun a ha =>
    have hb : □ (F a) := (ext (F a) True ⟨fun _ => trivial, fun _ => ha⟩) ▸ box_true
    ⟨fun x => x = a,
      le_of_box_incl (modal_K _ _ (nec% (fun (h : F a) (x : σ) (hx : x = a) => hx ▸ h)) hb),
      nec% ⟨a, rfl, fun _ hy => hy⟩⟩


/-! ### Well-orders (7–8 October 2026) -/

/-- In a well-order the minimal instance of a property is its least instance. -/
theorem least_of_minimal {σ : Type} [Ty σ] {R : σ → σ → Prop} (h : WellOrders R)
    {Y : σ → Prop} {m : σ} (hmin : ∀ y, Y y → R y m → y = m) : ∀ z, Y z → R m z :=
  fun z hz => (h.2.2.1 m z).elim id fun hzm => by
    rw [hmin z hz hzm]
    exact (h.2.2.1 m m).elim id id

/-- `well-ordering-r-implies-transversal-choice-r`: the least member of each cell. -/
theorem well_ordering_r_implies_transversal_choice_r {σ : Type} [Ty σ] :
    WellOrdering σ → TransversalChoice σ := fun ⟨R, hR⟩ E hE =>
  ⟨fun y => ∀ z, E y z → R y z, fun x =>
    (hR.2.2.2 (fun z => E x z) ⟨x, hE.1 x⟩).elim fun m ⟨hm, hmin⟩ =>
    have least := least_of_minimal hR hmin
    ⟨m, hm, fun z hz => least z (hE.2.2 x m z hm hz), fun z ⟨hxz, hFz⟩ =>
      hR.2.1 m z (least z hxz) (hFz m (hE.2.2 z x m (hE.2.1 x z hxz) hm))⟩⟩

/-- `necessary-well-ordering-r-implies-well-ordering-r`: `T`. -/
theorem necessary_well_ordering_r_implies_well_ordering_r {σ : Type} [Ty σ] :
    NecWellOrdering σ → WellOrdering σ := box_elim

/-- `necessary-well-ordering-r-implies-necessary-transversal-choice-r`. -/
theorem necessary_well_ordering_r_implies_necessary_transversal_choice_r {σ : Type} [Ty σ] :
    NecWellOrdering σ → NecTransversalChoice σ :=
  modal_K _ _ (nec% (well_ordering_r_implies_transversal_choice_r (σ := σ)))

/-- A well-order makes the least instance of an instantiated property its unique least
instance. -/
theorem unique_least {σ : Type} [Ty σ] (R : σ → σ → Prop) (F : σ → Prop) (h : WellOrders R)
    (hF : ∃ x, F x) : ∃ x, (F x ∧ ∀ y, F y → R x y) ∧ ∀ y, (F y ∧ ∀ z, F z → R y z) → y = x :=
  (h.2.2.2 F hF).elim fun m ⟨hm, hmin⟩ =>
    have least := least_of_minimal h hmin
    ⟨m, ⟨hm, least⟩, fun y hy => h.2.1 y m (hy.2 m hm) (least y hy.1)⟩

/-- `modal-well-ordering-r-implies-intensional-choice-r`: being the least instance. -/
theorem modal_well_ordering_r_implies_intensional_choice_r {σ : Type} [Ty σ] :
    ModalWellOrdering σ → IntensionalChoice σ := fun ⟨R, hR⟩ F hF =>
  ⟨fun x => F x ∧ ∀ y, F y → R x y,
   le_of_box_incl (nec% (fun (x : σ) (h : F x ∧ ∀ y, F y → R x y) => h.1)),
   modal_K _ _ (modal_K _ _ (nec% (unique_least R F)) hR) hF⟩

/-- Modal Well-Ordering is necessary, by `4`. -/
theorem box_modal_well_ordering {σ : Type} [Ty σ] (h : ModalWellOrdering σ) :
    □ (ModalWellOrdering σ) :=
  h.elim fun R hR => modal_K _ _
    (nec% (fun (h : □ (WellOrders R)) => (⟨R, h⟩ : ModalWellOrdering σ))) (modal_four _ hR)

/-- `modal-well-ordering-r-implies-necessary-intensional-choice-r`. -/
theorem modal_well_ordering_r_implies_necessary_intensional_choice_r {σ : Type} [Ty σ] :
    ModalWellOrdering σ → NecIntensionalChoice σ := fun h =>
  modal_K _ _ (nec% (modal_well_ordering_r_implies_intensional_choice_r (σ := σ)))
    (box_modal_well_ordering h)

/-- `modal-well-ordering-r-implies-necessary-well-ordering-r`. -/
theorem modal_well_ordering_r_implies_necessary_well_ordering_r {σ : Type} [Ty σ] :
    ModalWellOrdering σ → NecWellOrdering σ := fun ⟨R, hR⟩ =>
  modal_K _ _ (nec% (fun (h : WellOrders R) => (⟨R, h⟩ : WellOrdering σ))) hR

/-- Being a well-order depends only on the extension. -/
theorem wellOrders_of_iff {σ : Type} [Ty σ] (R R' : σ → σ → Prop) (he : ∀ x y, R' x y ↔ R x y)
    (h : WellOrders R) : WellOrders R' :=
  ⟨fun x y z a b => (he x z).2 (h.1 x y z ((he x y).1 a) ((he y z).1 b)),
   fun x y a b => h.2.1 x y ((he x y).1 a) ((he y x).1 b),
   fun x y => (h.2.2.1 x y).elim (fun a => Or.inl ((he x y).2 a)) (fun a => Or.inr ((he y x).2 a)),
   fun Y hY => (h.2.2.2 Y hY).elim fun x ⟨hx, hmin⟩ =>
     ⟨x, hx, fun y hy hyx => hmin y hy ((he y x).1 hyx)⟩⟩

/-- The relation defined from a unique well-order is a well-order. -/
theorem wellOrders_of_unique {σ : Type} [Ty σ] (G : (σ → σ → Prop) → Prop)
    (hG : ∀ R, G R → WellOrders R) (hu : ∃ R, G R ∧ ∀ R', G R' → R' = R) :
    WellOrders (fun x y => ∃ R, G R ∧ R x y) :=
  hu.elim fun R₀ ⟨h₀, hu₀⟩ => wellOrders_of_iff R₀ _
    (fun x y => ⟨fun ⟨R, hR, hxy⟩ => by rw [← hu₀ R hR]; exact hxy, fun hxy => ⟨R₀, h₀, hxy⟩⟩)
    (hG R₀ h₀)

/-- `necessary-well-ordering-and-intensional-choice-imply-modal-well-ordering`: Intensional
Choice at the type of relations picks a necessarily unique well-order, and the relation it
defines is necessarily a well-order. -/
theorem necessary_well_ordering_and_intensional_choice_imply_modal_well_ordering {σ : Type}
    [Ty σ] : NecWellOrdering σ → IntensionalChoice (σ → σ → Prop) → ModalWellOrdering σ :=
  fun hwo ic => (ic (fun R => WellOrders R) hwo).elim fun G ⟨hGF, hu⟩ =>
  ⟨fun x y => ∃ R, G R ∧ R x y, modal_K _ _ (modal_K _ _
    (nec% (fun (hGF : ∀ R : σ → σ → Prop, G R → WellOrders R)
        (hu : ∃ R, G R ∧ ∀ R', G R' → R' = R) => wellOrders_of_unique G hGF hu))
    ((le_iff G _).1 hGF)) hu⟩

end Classicism.Proofs
