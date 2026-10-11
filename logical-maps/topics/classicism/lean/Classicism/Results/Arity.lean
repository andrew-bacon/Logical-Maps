import Classicism.Tools.Schema
import Classicism.Certified.Schemas
import Classicism.Certified.Entailed
import Classicism.Results.Lists
import Classicism.Principles
import Classicism.Pointwise
import Classicism.Paper

-- goals and hover print `fun y ↦ …`, matching the source
set_option pp.unicode.fun true

/-!
# Results at every arity

The map states comprehension, Boolean Completeness, Atomicity and their kin for relations
of every arity, `∀^Ty σ̄`, and several of the paper's proofs reason about an argument tuple
`x̄`: "BF, one argument at a time", "the persistent coextension `λȳ. w ≤ X[ȳ]`". Two kinds
of shallow proof reach every arity:

- **pointwise reasoning at a relational type**: a theorem at a Rel-parameter `τ`, its
  pointwise steps through the laws of `Pointwise`, which the translator derives for every
  object type by induction on the type. It is at every arity already;
- **a unary proof**, at `σ → t`, for a result that uses BF over the tuple: vectorized in
  `σ` (its list rule), it holds at `σs ⇒* t` for every list, which is every relational
  type (`schema_subset_args`). BF at `σ` in such a proof becomes BF over the list, which
  BF gives (`P.Barcan.schema_entails_listSchema`); in `C5`, `□`BF at `σ` comes from `□ND`
  at `t` inside the proof, and the vectorized result has no list premise at all.

The file has three parts:

1. **The shallow layer**: the shallow cores at `τ`, the unary ones at `σ → t`, and the
   boxed step of Atomicity.
2. **Certification.** The certification command makes each a rule between schema
   instances, and, with a Ty-parameter, a list rule; the entailment command an entailment
   between schemas, and a list entailment.
3. **The metalogic**: the compositions of certified entailments, among them the ones in
   `Certified/Entailed.lean`, into the map's arrows. Each theorem here named by a map id
   is that record, for every arity.
-/

namespace Classicism
open Paper

/-! ## 1. The shallow layer -/

section shallowCores
variable {τ : Type} [Rel τ] [Pointwise τ]

/-- `w` an actual world gives `q ↔ □(¬w ∨ q)` for every `q`. -/
theorem actual_iff (w : Prop) (hw : ActualWorld w) : ∀ q : Prop, q ↔ □ (¬ w ∨ q) := fun q =>
  ⟨fun hq => modal_K _ _ (nec% (not_or_of_imp w q)) ((le_iff_prop w q).1 (hw.2 q hq)),
   fun h => Or.elim (box_elim h) (fun hn => absurd hw.1 hn) (fun hq => hq)⟩

/-- With `w` the actual world, `λx̄. □(¬w ∨ X[x̄])`, that is `λx̄. w ≤ X[x̄]`, is a persistent
coextension of `X` (Classicism, n. 38). -/
theorem persistent_coext_of_actual (X : τ) (w : Prop) (hw : ActualWorld w) :
    Persistent (boxAt (Rel.or (Rel.neg (constP w)) X)) ∧
      X ≡ boxAt (Rel.or (Rel.neg (constP w)) X) :=
  ⟨nec% (boxAt_four (Rel.or (Rel.neg (constP w)) X)), coext_boxAt_actual X w (actual_iff w hw)⟩

/-- `actuality-implies-persistent-comprehension-r`, at every relational type. -/
theorem actuality_implies_persistent_comprehension_r :
    P.Actuality → P.PersistentComprehension τ := fun act X =>
  act.elim fun w (hw : ActualWorld w) => ⟨_, persistent_coext_of_actual X w hw⟩

/-- If every truth is necessary, every relation is weakly inextensible. -/
theorem weaklyInextensible_of_all (X : τ) : (∀ p : Prop, p → □ p) → WeaklyInextensible X :=
  fun h Z hZ => h _ (incl_trans X (boxAt Z) Z hZ (boxAt_T Z))

/-- `extensionality-r-implies-rigid-comprehension-r`, at every arity: under the Fregean
Axiom (the nullary instance) every truth is necessary, and necessarily so; so every
relation is persistent and inextensible, and is its own rigid coextension. -/
theorem extensionality_r_implies_rigid_comprehension_r :
    P.Extensionality Prop → P.RigidComprehension τ := fun extP X =>
  have fa := Proofs.extensionality_r_implies_fregean_axiom extP
  have hall : □ (∀ p : Prop, p → □ p) := Proofs.box_of_fregean fa _ (Proofs.box_of_fregean fa)
  ⟨X, ⟨modal_K _ _ (nec% (incl_boxAt_of_all X)) hall,
      modal_K _ _ (nec% (weaklyInextensible_of_all X)) hall⟩, Rel.coext_refl X⟩

/-- In `C5` the negation of a persistent relation is persistent: where `Y` fails, `B` and
the persistence of `Y` make it fail necessarily, at every world. -/
theorem persistent_neg_of_c5 (Y : τ) :
    P.NecNecessityOfDistinctness Prop → Persistent Y → Persistent (Rel.neg Y) := fun hnd hP =>
  modal_K _ _ (modal_K _ _ (nec% (neg_incl_boxAt_of_b Y)) (Proofs.box_b_of_box_nd_t hnd))
    (modal_K _ _ (nec% (top_boxAt_of_box Y (boxAt Y))) (modal_four _ hP))

/-- `c5-and-persistent-comprehension-imply-gallin`, at every arity. -/
theorem c5_and_persistent_comprehension_imply_gallin :
    P.NecNecessityOfDistinctness Prop → P.PersistentComprehension τ →
      P.GallinExtensionalComprehension τ := fun hnd pc X =>
  (pc X).elim fun Y hY => ⟨Y, hY.1, persistent_neg_of_c5 Y hnd hY.1, hY.2⟩

/-- Rigid Comprehension gives Gallin's, in `C5`. -/
theorem c5_rigid_gallin :
    P.NecNecessityOfDistinctness Prop → P.RigidComprehension τ →
      P.GallinExtensionalComprehension τ := fun hnd rc =>
  c5_and_persistent_comprehension_imply_gallin hnd fun X => (rc X).elim fun Y hY => ⟨Y, hY.1.1, hY.2⟩

/-- `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension`, at every
arity: the last lemma necessitated, `□ND` boxed by `4`. -/
theorem c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension :
    P.NecNecessityOfDistinctness Prop → P.NecRigidComprehension τ →
      P.NecGallinExtensionalComprehension τ := fun hnd hrc =>
  modal_K _ _ (modal_K _ _ (nec% (c5_rigid_gallin (τ := τ))) (modal_four _ hnd)) hrc

/-- `necessary-actuality-implies-necessary-persistent-comprehension`. -/
theorem necessary_actuality_implies_necessary_persistent_comprehension :
    P.NecActuality → P.NecPersistentComprehension τ :=
  modal_K _ _ (nec% (actuality_implies_persistent_comprehension_r (τ := τ)))

/-- `c5-and-necessary-persistent-comprehension-imply-necessary-gallin`: the unboxed record
necessitated, `□ND` boxed by `4`. -/
theorem c5_and_necessary_persistent_comprehension_imply_necessary_gallin :
    P.NecNecessityOfDistinctness Prop → P.NecPersistentComprehension τ →
      P.NecGallinExtensionalComprehension τ := fun hnd hpc =>
  modal_K _ _ (modal_K _ _ (nec% (c5_and_persistent_comprehension_imply_gallin (τ := τ)))
    (modal_four _ hnd)) hpc

end shallowCores

section unary
variable {σ : Type} [Ty σ]

/-- With BF at `σ`, a property whose negation is weakly persistent is weakly inextensible:
where `Y` fails it fails necessarily, so `Y ⊆ □Z` gives `□(Y z → Z z)` at each `z`, and BF
boxes the quantifier. -/
theorem weaklyInextensible_of_neg_bf (Y : σ → Prop) :
    P.Barcan σ → WeaklyPersistent (¬ Y) → WeaklyInextensible Y := fun bf hn Z hZ =>
  bf (λ z ↦ Y z → Z z) fun z =>
    (em (Y z)).elim (fun hy => box_imp_of_box (Y z) (Z z) (hZ z hy))
      (fun hny => box_imp_of_box_not (Y z) (Z z) (hn z hny))

/-- Gallin Extensional Comprehension and BF give Weak Rigid Comprehension, at `σ → t`:
the Gallin-rigid coextension is persistent and, its negation being persistent, weakly
inextensible. -/
theorem gallin_bf_weak_rigid_comprehension :
    P.GallinExtensionalComprehension (σ → Prop) → P.Barcan σ →
      P.WeakRigidComprehension (σ → Prop) :=
  fun g bf X => (g X).elim fun Y hY =>
    ⟨Y, ⟨box_elim hY.1, weaklyInextensible_of_neg_bf Y bf (box_elim hY.2.1)⟩, hY.2.2⟩

/-- And in `C5`, Rigid Comprehension: the argument above under the box, with `□`BF at `σ`
from `□ND` at `t` (Proposition 2.3), the persistence of the negation being boxed
already. -/
theorem gallin_c5_rigid_comprehension :
    P.GallinExtensionalComprehension (σ → Prop) → P.NecNecessityOfDistinctness Prop →
      P.RigidComprehension (σ → Prop) :=
  fun g hnd X => (g X).elim fun Y hY =>
    ⟨Y, ⟨hY.1, modal_K _ _ (modal_K _ _ (nec% (weaklyInextensible_of_neg_bf Y))
      (Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r hnd)) hY.2.1⟩,
     hY.2.2⟩

/-- Boxed Gallin Extensional Comprehension gives `□`Rigid Comprehension in `C5`, at
`σ → t`: the last lemma necessitated, `□ND` boxed by `4`. -/
theorem nec_gallin_c5_nec_rigid_comprehension :
    P.NecGallinExtensionalComprehension (σ → Prop) → P.NecNecessityOfDistinctness Prop →
      P.NecRigidComprehension (σ → Prop) := fun hg hnd =>
  modal_K _ _ (modal_K _ _ (nec% (gallin_c5_rigid_comprehension (σ := σ))) hg)
    (modal_four _ hnd)

/-! ### Rigid Rigidity and Weakly Rigid Weak Rigidity, with BF (10 October 2026) -/

/-- Every relation entails `λz. ⊤`. -/
theorem le_top_unary (F : σ → Prop) : F ≤ (fun _ : σ => True) :=
  le_of_box_incl (nec% (fun (z : σ) (_ : F z) => trivial))

/-- With BF at `σ`, `λz. ⊤` is weakly rigid. -/
theorem weaklyRigid_top_of_bf : P.Barcan σ → WeaklyRigid (fun _ : σ => True) := fun bf =>
  ⟨fun _ _ => box_true, fun Z hZ =>
    bf (λ z ↦ True → Z z) fun z => box_imp_of_box True (Z z) (hZ z trivial)⟩

/-- The haecceity `λz. z = y` is rigid: persistent by the Necessity of Identity, and
inextensible since `□Zy` gives `□∀z. z = y → Zz`. -/
theorem rigid_haecceity (y : σ) : Rigid (fun z : σ => z = y) :=
  ⟨nec% (fun (z : σ) (h : z = y) => necessity_of_identity z y h),
   nec% (fun (Z : σ → Prop) (hZ : ∀ z : σ, z = y → □ (Z z)) =>
     modal_K _ _ (nec% (fun (h : Z y) (z : σ) (hz : z = y) => hz ▸ h)) (hZ y rfl))⟩

/-- `barcan-and-weakly-rigid-power-imply-weakly-rigid-weak-rigidity`, at `σ → t`: the power
property of the weakly rigid `λz. ⊤` is weak rigidity itself. -/
theorem bf_wrp_weakly_rigid_weak_rigidity :
    P.Barcan σ → P.WeaklyRigidPower (σ → Prop) → P.WeaklyRigidWeakRigidity (σ → Prop) :=
  fun bf wrp =>
  have heq : (fun X : σ → Prop => WeaklyRigid X ∧ X ≤ (fun _ : σ => True)) =
      (fun X : σ → Prop => WeaklyRigid X) :=
    le_antisymm_rel _ _
      (le_of_box_incl (nec% (fun (X : σ → Prop) (h : WeaklyRigid X ∧ X ≤ (fun _ : σ => True)) =>
        h.1)))
      (le_of_box_incl (nec% (fun (X : σ → Prop) (h : WeaklyRigid X) =>
        (⟨h, le_top_unary X⟩ : WeaklyRigid X ∧ X ≤ (fun _ : σ => True)))))
  show WeaklyRigid (fun X : σ → Prop => WeaklyRigid X) from
    heq ▸ wrp _ (weaklyRigid_top_of_bf bf)

/-- `rigid-rigidity-implies-necessary-barcan`, at `σ → t`: at every world, a property
necessary of everything is entailed by every rigid property, by the latter's weak
inextensibility; the weak inextensibility of rigidity carries this under the box, and every
individual has a rigid haecceity. -/
theorem rr_necessary_barcan : P.RigidRigidity (σ → Prop) → P.NecBarcan σ := fun h =>
  modal_K _ _
    (nec% (fun (wi : WeaklyInextensible (fun Z : σ → Prop => Rigid Z)) (X : σ → Prop)
        (hX : ∀ x : σ, □ (X x)) =>
      modal_K _ _
        (nec% (fun (hq : ∀ Z : σ → Prop, Rigid Z → ∀ y : σ, Z y → X y) (y : σ) =>
          hq (fun z : σ => z = y) (rigid_haecceity y) y rfl))
        (wi (fun Z : σ → Prop => ∀ y : σ, Z y → X y)
          (fun (Z : σ → Prop) (hZ : Rigid Z) =>
            weaklyInextensible_of_inextensible hZ.2 X (fun y _ => hX y)))))
    h.2

/-- `necessary-barcan-and-rigid-power-imply-rigid-rigidity`, at `σ → t`: □BF makes `λz. ⊤`
rigid, and its rigid power property is rigidity itself. -/
theorem nbf_rp_rigid_rigidity :
    P.NecBarcan σ → P.RigidPower (σ → Prop) → P.RigidRigidity (σ → Prop) := fun nbf rp =>
  have htop : Rigid (fun _ : σ => True) :=
    ⟨nec% (fun (_ : σ) (_ : True) => box_true),
     modal_K _ _ (nec% (fun (bf : P.Barcan σ) => (weaklyRigid_top_of_bf bf).2)) nbf⟩
  have heq : (fun X : σ → Prop => Rigid X ∧ X ≤ (fun _ : σ => True)) =
      (fun X : σ → Prop => Rigid X) :=
    le_antisymm_rel _ _
      (le_of_box_incl (nec% (fun (X : σ → Prop) (h : Rigid X ∧ X ≤ (fun _ : σ => True)) =>
        h.1)))
      (le_of_box_incl (nec% (fun (X : σ → Prop) (h : Rigid X) =>
        (⟨h, le_top_unary X⟩ : Rigid X ∧ X ≤ (fun _ : σ => True)))))
  show Rigid (fun X : σ → Prop => Rigid X) from heq ▸ rp _ htop

/-! ### ND, Strong Actuality and Gallin (11 October 2026) -/

/-- A possible `w` entailing `¬q` does not entail `q`. -/
theorem not_le_of_dia_le_neg (w q : Prop) (hd : ◇ w) (h : w ≤ ¬ q) : ¬ (w ≤ q) := fun h' =>
  hd (Eq.mp (box_not_eq w) (modal_K _ _ (modal_K _ _
    (nec% (fun (a : w → q) (b : w → ¬ q) (hw : w) => b hw (a hw)))
    ((le_iff_prop w q).1 h')) ((le_iff_prop w (¬ q)).1 h)))

/-- `nd-and-strong-actuality-imply-gallin-comprehension`, at `σ → t` (Cian Dorr): for `w`
witnessing Strong Actuality, `λz. w ≤ Xz` is coextensive with `X`, persistent by `4`, and has
a persistent negation by `B` (from ND at `t`) and the boxed decisions of `w`. -/
theorem nd_strong_actuality_gallin :
    P.NecessityOfDistinctness Prop → P.StrongActuality →
      P.GallinExtensionalComprehension (σ → Prop) := fun nd sa X =>
  sa.elim fun w hw =>
  have hb : □ (◇ w) :=
    Proofs.modal_five_implies_modal_b (Proofs.distinctness_necessary_t_implies_modal_five nd) w hw.1
  ⟨fun z => w ≤ X z,
   nec% (fun (z : σ) (h : w ≤ X z) => box_le_prop w (X z) h),
   modal_K _ _ (modal_K _ _
     (nec% (fun (hb : □ (◇ w)) (hd : ∀ q : Prop, w ≤ q ∨ w ≤ ¬ q) (z : σ) (hn : ¬ (w ≤ X z)) =>
       (hd (X z)).elim (fun h => absurd h hn) fun h =>
         modal_K _ _ (modal_K _ _ (nec% (not_le_of_dia_le_neg w (X z))) hb)
           (box_le_prop w (¬ X z) h)))
     (modal_four _ hb)) hw.2,
   fun z => ⟨fun hx => (box_elim hw.2 (X z)).elim id
       fun h => absurd hx (imp_of_le_prop w (¬ X z) h hw.1),
     fun h => imp_of_le_prop w (X z) h hw.1⟩⟩

/-- `c5-and-necessary-strong-actuality-imply-necessary-gallin-comprehension`, at `σ → t`. -/
theorem c5_nec_strong_actuality_nec_gallin :
    P.NecNecessityOfDistinctness Prop → P.NecStrongActuality →
      P.NecGallinExtensionalComprehension (σ → Prop) := fun h₁ h₂ =>
  modal_K _ _ (modal_K _ _ (nec% (nd_strong_actuality_gallin (σ := σ))) h₁) h₂

end unary

/-- In `C5`, `□`Boolean Completeness gives `□`Plenitude, for relations `σ → (σ' → t) → t`:
Proposition 2.14 necessitated, `□ND` boxed by `4`. -/
theorem necessary_completeness_c5_necessary_plenitude {σ' σ : Type} [Ty σ'] [Ty σ] :
    P.NecBooleanCompleteness (σ → σ' → Prop) → P.NecNecessityOfDistinctness Prop →
      P.NecPlenitude σ (σ' → Prop) := fun hbc hnd =>
  modal_K _ _ (modal_K _ _ (nec% (Proofs.c5_and_completeness_imply_plenitude (σ' := σ') (σ := σ)))
    hbc) (modal_four _ hnd)

/-- The boxed step of Atomicity: `□`Atomicity at `t` and `□`BF at `σ` give `□`Atomicity at
`σ → t`, the record `atomicity-t-and-bf-imply-atomicity` at `σ → t` necessitated. -/
theorem necAtomicity_step {σ : Type} [Ty σ] :
    P.NecAtomicity Prop → P.NecBarcan σ → P.NecAtomicity (σ → Prop) := fun h₁ h₂ =>
  modal_K _ _ (modal_K _ _ (nec% (Proofs.atomicity_t_and_bf_imply_atomicity (σ := σ))) h₁) h₂

/-- Atomicity at `t` read as the instance of Atomicity is Atomicity at `t` in the map's own
spelling, as a rule (the `C5` records conclude with the instance). -/
theorem atomicityT_of_atomicity_at_t : P.Atomicity Prop → P.AtomicityT := fun h => h

/-- In `C5`, `□`Actuality gives `□`Atomicity at `t`: Proposition 2.6 at `t`, necessitated. -/
theorem c5_necessary_atomicity_t :
    P.NecActuality → P.NecNecessityOfDistinctness Prop → P.NecAtomicity Prop := fun hna hnd =>
  modal_K _ _ (modal_K _ _ (nec% Proofs.c5_and_necessary_actuality_imply_atomicity_at_t)
    (modal_four _ hna)) (modal_four _ hnd)

/-- Under the Fregean Axiom a truth is necessary, Actuality among them. -/
theorem fregean_actuality_necessary_actuality : P.FregeanAxiom → P.Actuality → P.NecActuality :=
  fun fa act => fa _ True ⟨fun _ => trivial, fun _ => act⟩

/-! ## 2. Certification -/

#classicism_certify Classicism.actuality_implies_persistent_comprehension_r
  Classicism.necessary_actuality_implies_necessary_persistent_comprehension
  Classicism.c5_and_necessary_persistent_comprehension_imply_necessary_gallin
  Classicism.nd_strong_actuality_gallin Classicism.c5_nec_strong_actuality_nec_gallin
  Classicism.bf_wrp_weakly_rigid_weak_rigidity Classicism.rr_necessary_barcan
  Classicism.nbf_rp_rigid_rigidity
  Classicism.gallin_bf_weak_rigid_comprehension Classicism.gallin_c5_rigid_comprehension
  Classicism.nec_gallin_c5_nec_rigid_comprehension
  Classicism.necAtomicity_step Classicism.atomicityT_of_atomicity_at_t
  Classicism.c5_necessary_atomicity_t Classicism.fregean_actuality_necessary_actuality
  Classicism.extensionality_r_implies_rigid_comprehension_r
  Classicism.c5_and_persistent_comprehension_imply_gallin
  Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension
  Classicism.necessary_completeness_c5_necessary_plenitude

#classicism_entails Classicism.actuality_implies_persistent_comprehension_r
  Classicism.necessary_actuality_implies_necessary_persistent_comprehension
  Classicism.c5_and_necessary_persistent_comprehension_imply_necessary_gallin
  Classicism.nd_strong_actuality_gallin Classicism.c5_nec_strong_actuality_nec_gallin
  Classicism.bf_wrp_weakly_rigid_weak_rigidity Classicism.rr_necessary_barcan
  Classicism.nbf_rp_rigid_rigidity
  Classicism.gallin_bf_weak_rigid_comprehension Classicism.gallin_c5_rigid_comprehension
  Classicism.nec_gallin_c5_nec_rigid_comprehension
  Classicism.c5_necessary_atomicity_t Classicism.fregean_actuality_necessary_actuality
  Classicism.extensionality_r_implies_rigid_comprehension_r
  Classicism.c5_and_persistent_comprehension_imply_gallin
  Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension
  Classicism.necessary_completeness_c5_necessary_plenitude

/-! ## 3. The metalogic -/

namespace Meta
open AxiomSet

/-- `classicism-implies-existence-r`, at every type: the instance at `e` (the axiom
`e_exists`) and those at relational types (theorems of `C⁻`), the two records. -/
theorem classicism_implies_existence_r : empty ⟹ P.Existence.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  cases σ with
  | e => exact Proofs.classicism_implies_existence_r_at_e.entails _ rfl
  | rel ρ => exact Proofs.classicism_implies_existence_r_relational.entails _ ⟨ρ, hσ, rfl⟩
  | var i => exact hσ.elim

/-- `actuality-implies-persistent-comprehension-r`, the map's record, at every arity. -/
theorem actuality_implies_persistent_comprehension_r :
    P.Actuality.schema ⟹ P.PersistentComprehension.schema :=
  Classicism.actuality_implies_persistent_comprehension_r.entails

/-- `c5-and-actuality-imply-rigid-comprehension` (Proposition 2.10), at every arity: the
record at `σ → t`, vectorized. -/
theorem c5_and_actuality_imply_rigid_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.Actuality.schema ⟹ P.RigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      Proofs.c5_and_actuality_imply_rigid_comprehension.listEntails)

/-- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`, at every arity: the core
at `σ → t`, vectorized, with BF over every list from BF. -/
theorem gallin_comprehension_and_bf_imply_weak_rigid_comprehension :
    P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.WeakRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.union_left _ _)
        (Entails.trans (Entails.union_right _ _) P.Barcan.schema_entails_listSchema))
      gallin_bf_weak_rigid_comprehension.listEntails)

/-- `gallin-comprehension-and-bf-imply-rigid-comprehension`, at every arity: Gallin gives
ND, ND and BF give `□ND`, and the core at `σ → t`, vectorized. -/
theorem gallin_comprehension_and_bf_imply_rigid_comprehension :
    P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹ P.RigidComprehension.schema :=
  have nd : P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.NecessityOfDistinctness.schema :=
    Entails.trans (Entails.union_left _ _) Proofs.gallin_comprehension_implies_nd.entails
  have nnd : P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.NecNecessityOfDistinctness.schema :=
    Entails.trans (Entails.union nd (Entails.union_right _ _))
      Proofs.nd_and_bf_imply_necessary_nd.entails
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_left _ _) nnd)
      gallin_c5_rigid_comprehension.listEntails)

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension`, at every arity: the record at
`σ → t`, from Atomicity at `t`, vectorized. -/
theorem c5_and_atomicity_imply_necessary_rigid_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      P.NecRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      Proofs.c5_and_atomicity_imply_necessary_rigid_comprehension.listEntails)

/-- `atomicity-t-and-bf-imply-atomicity`, at every arity: the record at `σ → t`, vectorized,
with BF over every list from BF. -/
theorem atomicity_t_and_bf_imply_atomicity :
    P.AtomicityT.schema ∪ P.Barcan.schema ⟹ P.Atomicity.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_left _ _)
        (Entails.trans (Entails.union_right _ _) P.Barcan.schema_entails_listSchema))
      Proofs.atomicity_t_and_bf_imply_atomicity.listEntails)

/-- The same, with Atomicity at `t` read as the instance of Atomicity, the form the `C5`
records conclude with. -/
theorem atomicity_of_atomicity_at_t_barcan :
    single (P.Atomicity.quoted RTy.t) ∪ P.Barcan.schema ⟹ P.Atomicity.schema :=
  Entails.trans
    (Entails.union
      (by rintro a rfl
          exact (Theorem.ofC atomicityT_of_atomicity_at_t.rule).mp (Theorem.ax (Or.inl rfl)))
      (Entails.union_right _ _))
    atomicity_t_and_bf_imply_atomicity

/-- `c5-and-necessary-actuality-imply-atomicity` (Proposition 2.6, right to left), at every
arity: Atomicity at `t` from the `t` record, BF from `□ND`, and the induction. -/
theorem c5_and_necessary_actuality_imply_atomicity :
    P.NecNecessityOfDistinctness.schema ∪ P.NecActuality.schema ⟹ P.Atomicity.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
        Proofs.c5_and_necessary_actuality_imply_atomicity_at_t.entails)
      (Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails))
    atomicity_of_atomicity_at_t_barcan

/-- `c5-and-necessary-completeness-imply-atomicity` (Proposition 2.6), at every arity. -/
theorem c5_and_necessary_completeness_imply_atomicity :
    P.NecNecessityOfDistinctness.schema ∪ P.NecBooleanCompleteness.schema ⟹
      P.Atomicity.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
        Proofs.c5_and_necessary_completeness_imply_atomicity_at_t.entails)
      (Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails))
    atomicity_of_atomicity_at_t_barcan

/-- **`□`Atomicity at `t` and `□`BF entail `□`Atomicity**: the boxed step, vectorized, with
`□`BF over every list from `□`BF. -/
theorem necAtomicity_of_at_t_necBarcan :
    single (P.NecAtomicity.quoted RTy.t) ∪ P.NecBarcan.schema ⟹ P.NecAtomicity.schema := by
  refine Entails.mono_right (schema_subset_args _) ?_
  rintro a ⟨σs, hσs, rfl⟩
  exact (Theorem.ofC (necAtomicity_step.listRule σs)).mp₂ (Theorem.ax (Or.inl rfl))
    (Entails.mono_left (fun _ => Or.inr) P.NecBarcan.schema_entails_listSchema _ ⟨σs, hσs, rfl⟩)

/-- `c5-and-atomicity-imply-necessary-atomicity` (Proposition 2.6 with 2.7), at every
arity: Atomicity and BF give `□`Actuality, which with `□ND` gives `□`Atomicity at `t`,
and `□`BF, from `□ND`, carries it to every type. -/
theorem c5_and_atomicity_imply_necessary_atomicity :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.NecAtomicity.schema :=
  have bf : P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.Barcan.schema :=
    Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails
  have na : P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      single P.NecActuality.quoted :=
    Entails.trans (Entails.union (Entails.union_right _ _) bf)
      Proofs.atomicity_and_bf_imply_necessary_actuality.entails
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union na (Entails.union_left _ _)) c5_necessary_atomicity_t.entails)
      (Entails.trans (Entails.union_left _ _)
        Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r.entails))
    necAtomicity_of_at_t_necBarcan

/-- `extensionality-r-implies-atomicity-r`, at every arity: Extensionality gives the
Fregean Axiom and Actuality; the Fregean Axiom gives `□ND` and makes Actuality necessary;
and in `C5` `□`Actuality gives Atomicity. -/
theorem extensionality_r_implies_atomicity_r :
    P.Extensionality.schema ⟹ P.Atomicity.schema :=
  have fa : P.Extensionality.schema ⟹ single P.FregeanAxiom.quoted :=
    Proofs.extensionality_r_implies_fregean_axiom.entails
  have act : P.Extensionality.schema ⟹ single P.Actuality.quoted :=
    Proofs.extensionality_r_implies_actuality.entails
  Entails.trans
    (Entails.union (Entails.trans fa Proofs.fregean_axiom_implies_necessary_distinctness_necessary_r.entails)
      (Entails.trans (Entails.union fa act) fregean_actuality_necessary_actuality.entails))
    c5_and_necessary_actuality_imply_atomicity

/-- `necessary-gallin-comprehension-implies-necessary-rigid-comprehension`, at every arity:
`□`Gallin gives `□ND`, and the boxed core at `σ → t`, vectorized. -/
theorem necessary_gallin_comprehension_implies_necessary_rigid_comprehension :
    P.NecGallinExtensionalComprehension.schema ⟹ P.NecRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.refl _)
        Proofs.necessary_gallin_comprehension_implies_necessary_nd.entails)
      nec_gallin_c5_nec_rigid_comprehension.listEntails)

/-- `necessary-plenitude-r-implies-atomicity-r` (Propositions 2.13, 2.15 and 2.6 boxed),
at every arity: `□`Plenitude gives `□ND` and `□`Actuality, and in `C5` `□`Actuality gives
Atomicity. -/
theorem necessary_plenitude_r_implies_atomicity_r :
    P.NecPlenitude.schema ⟹ P.Atomicity.schema :=
  Entails.trans
    (Entails.union Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r.entails
      Proofs.necessary_plenitude_r_implies_necessary_actuality.entails)
    c5_and_necessary_actuality_imply_atomicity

/-- `necessary-plenitude-r-implies-necessary-atomicity-r`, at every arity. -/
theorem necessary_plenitude_r_implies_necessary_atomicity_r :
    P.NecPlenitude.schema ⟹ P.NecAtomicity.schema :=
  Entails.trans
    (Entails.union Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r.entails
      necessary_plenitude_r_implies_atomicity_r)
    c5_and_atomicity_imply_necessary_atomicity

/-! ### Boolean Completeness, Plenitude and the haecceities

The records at `σ → t` in `Results/Records.lean` whose greatest lower bounds are pointwise
meets `λz. ∀Y. X*Y → Yz`, or whose witnesses are haecceities `λx. u = x`, vectorized; and
the Plenitude records for output `σ' → t`, vectorized in `σ'`, every output type being
`σs ⇒* t`. -/

/-- `weak-rigid-comprehension-r-implies-boolean-completeness-r`, at every arity. -/
theorem weak_rigid_comprehension_r_implies_boolean_completeness_r :
    P.WeakRigidComprehension.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.weak_rigid_comprehension_r_implies_boolean_completeness_r.listEntails

/-- `rigid-comprehension-r-implies-boolean-completeness-r` (Proposition 2.8), at every
arity. -/
theorem rigid_comprehension_r_implies_boolean_completeness_r :
    P.RigidComprehension.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.rigid_comprehension_r_implies_boolean_completeness_r.listEntails

/-- `extensionality-r-implies-boolean-completeness-r`, at every arity. -/
theorem extensionality_r_implies_boolean_completeness_r :
    P.Extensionality.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.extensionality_r_implies_boolean_completeness_r.listEntails

/-- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r`, at every
arity. -/
theorem necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r :
    P.NecRigidComprehension.schema ⟹ P.NecBooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r.listEntails

/-- `c5-and-actuality-imply-completeness` (Proposition 2.5, right to left), at every arity:
Rigid Comprehension (Proposition 2.10), then Proposition 2.8. -/
theorem c5_and_actuality_imply_completeness :
    P.NecNecessityOfDistinctness.schema ∪ P.Actuality.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.trans c5_and_actuality_imply_rigid_comprehension
    rigid_comprehension_r_implies_boolean_completeness_r

/-- `c5-and-atomicity-imply-necessary-completeness` (Proposition 2.6), at every arity:
`□`Rigid Comprehension, then Proposition 2.8 boxed. -/
theorem c5_and_atomicity_imply_necessary_completeness :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      P.NecBooleanCompleteness.schema :=
  Entails.trans c5_and_atomicity_imply_necessary_rigid_comprehension
    necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r

/-- `completeness-and-actuality-imply-weak-rigid-comprehension`, at every arity: the least
upper bound of the haecceities. -/
theorem completeness_and_actuality_imply_weak_rigid_comprehension :
    P.BooleanCompleteness.schema ∪ P.Actuality.schema ⟹ P.WeakRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.completeness_and_actuality_imply_weak_rigid_comprehension.listEntails

/-- `c5-and-completeness-imply-plenitude` (Proposition 2.14), at every output type. -/
theorem c5_and_completeness_imply_plenitude :
    P.NecNecessityOfDistinctness.schema ∪ P.BooleanCompleteness.schema ⟹ P.Plenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      Proofs.c5_and_completeness_imply_plenitude.listEntails)

/-- `rigid-comprehension-and-nd-imply-plenitude` (Proposition 2.16), at every output
type. -/
theorem rigid_comprehension_and_nd_imply_plenitude :
    P.RigidComprehension.schema ∪ P.NecessityOfDistinctness.schema ⟹ P.Plenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    Proofs.rigid_comprehension_and_nd_imply_plenitude.listEntails

/-- `extensionality-r-implies-plenitude-r`, at every output type: Extensionality gives the
Fregean Axiom, hence `□ND`, and Boolean Completeness, and Proposition 2.14. -/
theorem extensionality_r_implies_plenitude_r :
    P.Extensionality.schema ⟹ P.Plenitude.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans Proofs.extensionality_r_implies_fregean_axiom.entails
        Proofs.fregean_axiom_implies_necessary_distinctness_necessary_r.entails)
      extensionality_r_implies_boolean_completeness_r)
    c5_and_completeness_imply_plenitude

/-- `c5-and-atomicity-imply-necessary-plenitude`, at every output type: `□`Boolean
Completeness (Proposition 2.6) and Proposition 2.14 boxed. -/
theorem c5_and_atomicity_imply_necessary_plenitude :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.NecPlenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    (Entails.trans
      (Entails.union c5_and_atomicity_imply_necessary_completeness (Entails.union_left _ _))
      necessary_completeness_c5_necessary_plenitude.listEntails)

/-- `actual-profile-r-implies-actuality`: Actual Profile over the empty list of argument
types is Actuality, on the nose. -/
theorem actual_profile_r_implies_actuality :
    P.ActualProfile.listSchema ⟹ P.Actuality.schema := by
  rintro a rfl
  exact Theorem.ax ⟨[], by simp [Ty.AllClosed], rfl⟩

/-! ### Weakly Inextensible and Inextensible Comprehension, Modalized Plenitude

The records of 25–28 September proved at `σ → t` (output `σ' → t` for Modalized
Plenitude) in `Results/Records.lean`, vectorized. -/

/-- `actuality-implies-weakly-inextensible-comprehension-r`, at every arity. -/
theorem actuality_implies_weakly_inextensible_comprehension_r :
    P.Actuality.schema ⟹ P.WeaklyInextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.actuality_implies_weakly_inextensible_comprehension_r.listEntails

/-- `necessary-actuality-implies-necessary-weakly-inextensible-comprehension-r`, at every
arity. -/
theorem necessary_actuality_implies_necessary_weakly_inextensible_comprehension_r :
    P.NecActuality.schema ⟹ P.NecWeaklyInextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_actuality_implies_necessary_weakly_inextensible_comprehension_r.listEntails

/-- `boolean-completeness-r-implies-weakly-inextensible-comprehension-r`, at every arity: the
least upper bound of the haecceities. -/
theorem boolean_completeness_r_implies_weakly_inextensible_comprehension_r :
    P.BooleanCompleteness.schema ⟹ P.WeaklyInextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.boolean_completeness_r_implies_weakly_inextensible_comprehension_r.listEntails

/-- `actuality-and-bf-imply-inextensible-comprehension`, at every arity: BF at the type of
relations, and over the list of argument types. -/
theorem actuality_and_bf_imply_inextensible_comprehension :
    P.Actuality.schema ∪ P.Barcan.schema ⟹ P.InextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.refl _)
        (Entails.trans (Entails.union_right _ _) P.Barcan.schema_entails_listSchema))
      Proofs.actuality_and_bf_imply_inextensible_comprehension.listEntails)

/-- `necessary-bf-and-actuality-imply-inextensible-comprehension`, at every arity. -/
theorem necessary_bf_and_actuality_imply_inextensible_comprehension :
    P.NecBarcan.schema ∪ P.Actuality.schema ⟹ P.InextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union
        (Entails.trans (Entails.union_left _ _) P.NecBarcan.schema_entails_listSchema)
        (Entails.union_right _ _))
      Proofs.necessary_bf_and_actuality_imply_inextensible_comprehension.listEntails)

/-- `actuality-and-distinctness-preserving-collapse-imply-inextensible-comprehension`, at
every arity. -/
theorem actuality_and_distinctness_preserving_collapse_imply_inextensible_comprehension :
    P.Actuality.schema ∪ P.DistinctnessPreservingCollapse.schema ⟹
      P.InextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.actuality_and_distinctness_preserving_collapse_imply_inextensible_comprehension.listEntails

/-- `classicism-implies-modalized-plenitude-r`, at every output type. -/
theorem classicism_implies_modalized_plenitude_r :
    AxiomSet.empty ⟹ P.ModalizedPlenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    Proofs.classicism_implies_modalized_plenitude_r.listEntails

/-! ### Strong Leibniz

The records at `σ → t` in `Results/Records.lean`, vectorized. -/

/-- `strong-leibniz-r-implies-atomicity-r`, at every arity. -/
theorem strong_leibniz_r_implies_atomicity_r :
    P.StrongLeibniz.schema ⟹ P.Atomicity.schema :=
  Entails.mono_right (schema_subset_args _) Proofs.strong_leibniz_r_implies_atomicity_r.listEntails

/-- `atomicity-and-bf-imply-strong-leibniz`, at every arity. -/
theorem atomicity_and_bf_imply_strong_leibniz :
    P.Atomicity.schema ∪ P.Barcan.schema ⟹ P.StrongLeibniz.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.atomicity_and_bf_imply_strong_leibniz.listEntails

/-- `necessary-strong-leibniz-implies-necessary-atomicity`, at every arity. -/
theorem necessary_strong_leibniz_implies_necessary_atomicity :
    P.NecStrongLeibniz.schema ⟹ P.NecAtomicity.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_strong_leibniz_implies_necessary_atomicity.listEntails

/-- `necessary-atomicity-and-necessary-bf-imply-necessary-strong-leibniz`, at every arity. -/
theorem necessary_atomicity_and_necessary_bf_imply_necessary_strong_leibniz :
    P.NecAtomicity.schema ∪ P.NecBarcan.schema ⟹ P.NecStrongLeibniz.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_atomicity_and_necessary_bf_imply_necessary_strong_leibniz.listEntails

/-- `necessary-strong-leibniz-t-and-necessary-bf-imply-necessary-strong-leibniz`, at every
arity: `□`BF over the list of argument types, from `□`BF. -/
theorem necessary_strong_leibniz_t_and_necessary_bf_imply_necessary_strong_leibniz :
    P.NecStrongLeibnizT.schema ∪ P.NecBarcan.schema ⟹ P.NecStrongLeibniz.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.union_left _ _)
        (Entails.trans (Entails.union_right _ _) P.NecBarcan.schema_entails_listSchema))
      Proofs.necessary_strong_leibniz_t_and_necessary_bf_imply_necessary_strong_leibniz.listEntails)


/-! ### Boxed forms, at every arity (6 October 2026) -/

/-- `necessary-atomicity-t-and-necessary-bf-imply-necessary-atomicity`, at every arity. -/
theorem necessary_atomicity_t_and_necessary_bf_imply_necessary_atomicity :
    P.NecAtomicityT.schema ∪ P.NecBarcan.schema ⟹ P.NecAtomicity.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_left _ _)
        (Entails.trans (Entails.union_right _ _) P.NecBarcan.schema_entails_listSchema))
      Proofs.necessary_atomicity_t_and_necessary_bf_imply_necessary_atomicity.listEntails)

/-- `necessary-actuality-and-necessary-bf-imply-necessary-inextensible-comprehension`, at every
arity. -/
theorem necessary_actuality_and_necessary_bf_imply_necessary_inextensible_comprehension :
    P.NecActuality.schema ∪ P.NecBarcan.schema ⟹ P.NecInextensibleComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.refl _)
        (Entails.trans (Entails.union_right _ _) P.NecBarcan.schema_entails_listSchema))
      Proofs.necessary_actuality_and_necessary_bf_imply_necessary_inextensible_comprehension.listEntails)

/-- `necessary-completeness-and-necessary-actuality-imply-necessary-weak-rigid-comprehension`,
at every arity. -/
theorem necessary_completeness_and_necessary_actuality_imply_necessary_weak_rigid_comprehension :
    P.NecBooleanCompleteness.schema ∪ P.NecActuality.schema ⟹ P.NecWeakRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_completeness_and_necessary_actuality_imply_necessary_weak_rigid_comprehension.listEntails


/-- `c5-implies-necessary-rigid-power`, at every arity: the core at `σ → t`, vectorized. -/
theorem c5_implies_necessary_rigid_power :
    P.NecNecessityOfDistinctness.schema ⟹ P.NecRigidPower.schema :=
  Entails.mono_right (schema_subset_args _) Proofs.c5_implies_necessary_rigid_power.listEntails


/-- `c5-implies-tame-rigidity`, at every arity. -/
theorem c5_implies_tame_rigidity : P.NecNecessityOfDistinctness.schema ⟹ P.TameRigidity.schema :=
  Entails.mono_right (schema_subset_args _) Proofs.c5_implies_tame_rigidity.listEntails

/-- `c5-implies-necessary-tame-rigidity`, at every arity. -/
theorem c5_implies_necessary_tame_rigidity :
    P.NecNecessityOfDistinctness.schema ⟹ P.NecTameRigidity.schema :=
  Entails.mono_right (schema_subset_args _) Proofs.c5_implies_necessary_tame_rigidity.listEntails


/-! ### Rigid Rigidity and Weakly Rigid Weak Rigidity, at every arity (10 October 2026) -/

/-- `barcan-and-weakly-rigid-power-imply-weakly-rigid-weak-rigidity`, at every arity: the core
at `σ → t`, vectorized, with BF over every list from BF. -/
theorem barcan_and_weakly_rigid_power_imply_weakly_rigid_weak_rigidity :
    P.Barcan.schema ∪ P.WeaklyRigidPower.schema ⟹ P.WeaklyRigidWeakRigidity.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union
        (Entails.trans (Entails.union_left _ _) P.Barcan.schema_entails_listSchema)
        (Entails.union_right _ _))
      bf_wrp_weakly_rigid_weak_rigidity.listEntails)

/-- `barcan-and-weakly-rigid-power-imply-necessary-tame-rigidity`, at every arity: through
Weakly Rigid Weak Rigidity. -/
theorem barcan_and_weakly_rigid_power_imply_necessary_tame_rigidity :
    P.Barcan.schema ∪ P.WeaklyRigidPower.schema ⟹ P.NecTameRigidity.schema :=
  Entails.trans barcan_and_weakly_rigid_power_imply_weakly_rigid_weak_rigidity
    Proofs.weakly_rigid_weak_rigidity_implies_necessary_tame_rigidity.entails

/-- `rigid-rigidity-implies-necessary-barcan`: Rigid Rigidity at `σ → t` gives □BF at `σ`. -/
theorem rigid_rigidity_implies_necessary_barcan :
    P.RigidRigidity.schema ⟹ P.NecBarcan.schema :=
  rr_necessary_barcan.entails

/-- `necessary-barcan-and-rigid-power-imply-rigid-rigidity`, at every arity: the core at
`σ → t`, vectorized, with □BF over every list from □BF. -/
theorem necessary_barcan_and_rigid_power_imply_rigid_rigidity :
    P.NecBarcan.schema ∪ P.RigidPower.schema ⟹ P.RigidRigidity.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union
        (Entails.trans (Entails.union_left _ _) P.NecBarcan.schema_entails_listSchema)
        (Entails.union_right _ _))
      nbf_rp_rigid_rigidity.listEntails)


/-! ### BF at the relational types; ND, Strong Actuality and Gallin (11 October 2026) -/

/-- `atomicity-and-bf-relational-imply-strong-leibniz`, at every arity. -/
theorem atomicity_and_bf_relational_imply_strong_leibniz :
    P.Atomicity.schema ∪ P.BarcanRelational.schema ⟹ P.StrongLeibniz.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.atomicity_and_bf_relational_imply_strong_leibniz.listEntails

/-- `necessary-atomicity-and-necessary-bf-relational-imply-necessary-strong-leibniz`, at every
arity. -/
theorem necessary_atomicity_and_necessary_bf_relational_imply_necessary_strong_leibniz :
    P.NecAtomicity.schema ∪ P.NecBarcanRelational.schema ⟹ P.NecStrongLeibniz.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_atomicity_and_necessary_bf_relational_imply_necessary_strong_leibniz.listEntails

/-- `nd-and-strong-actuality-imply-gallin-comprehension`, at every arity. -/
theorem nd_and_strong_actuality_imply_gallin_comprehension :
    P.NecessityOfDistinctness.schema ∪ P.StrongActuality.schema ⟹
      P.GallinExtensionalComprehension.schema :=
  Entails.mono_right (schema_subset_args _) nd_strong_actuality_gallin.listEntails

/-- `c5-and-necessary-strong-actuality-imply-necessary-gallin-comprehension`, at every arity. -/
theorem c5_and_necessary_strong_actuality_imply_necessary_gallin_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.NecStrongActuality.schema ⟹
      P.NecGallinExtensionalComprehension.schema :=
  Entails.mono_right (schema_subset_args _) c5_nec_strong_actuality_nec_gallin.listEntails

end Meta

end Classicism
