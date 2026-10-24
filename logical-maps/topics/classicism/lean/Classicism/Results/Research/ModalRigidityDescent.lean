import Classicism.Results.Records.Lattice
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem

/-!
# Rigid indexed unions, direct images and descent along necessary embeddings

New research continuation, 22 October 2026. Direct proof notes and exact
certification status: research/2026-10-22/lean-formalization/
modal-rigidity-descent.md and modal-descent-status.md.

No BF, choice, ND or comprehension is used in the closure theorems.
The final descent theorem assumes its displayed comprehension instance.
All types and formulas are in the original finitary C.
-/

namespace Classicism.Research.ModalRigidityDescent
open Classicism.P Classicism.Paper

theorem rigid_necessary {ρ : Type} [Rel ρ] (R : ρ) (h : Rigid R) : □ (Rigid R) :=
  modal_K _ _ (nec% (rigid_iff_box_weaklyRigid R).2)
    (modal_four _ ((rigid_iff_box_weaklyRigid R).1 h))

section indexedUnion
variable {σ τ : Type} [Ty σ] [Ty τ]

def IndexedUnion (R : σ → Prop) (F : σ → τ → Prop) : τ → Prop :=
  fun y => ∃ x, R x ∧ F x y

theorem rigid_family_sealed (R : σ → Prop) (F : σ → τ → Prop) (hR : Rigid R)
    (hF : ∀ x, R x → Rigid (F x)) : □ (∀ x, R x → Rigid (F x)) :=
  weaklyInextensible_of_inextensible hR.2 (fun x => Rigid (F x))
    fun x hx => rigid_necessary (F x) (hF x hx)

theorem indexed_union_weakly_persistent (R : σ → Prop) (F : σ → τ → Prop)
    (hR : WeaklyPersistent R) (hF : ∀ x, R x → WeaklyPersistent (F x)) :
    WeaklyPersistent (IndexedUnion R F) := fun y hy =>
  hy.elim fun x hx =>
    modal_K _ _ (modal_K _ _
      (nec% (fun (hr : R x) (hf : F x y) => (show IndexedUnion R F y from ⟨x, hr, hf⟩)))
      (hR x hx.1)) (hF x hx.1 y hx.2)

theorem indexed_union_weakly_inextensible (R : σ → Prop) (F : σ → τ → Prop)
    (hR : WeaklyInextensible R) (hF : ∀ x, R x → WeaklyInextensible (F x)) :
    WeaklyInextensible (IndexedUnion R F) := fun Z hZ =>
  have hall : □ (∀ x, R x → ∀ y, F x y → Z y) :=
    hR (fun x => ∀ y, F x y → Z y) fun x hx =>
      hF x hx Z fun y hy => hZ y ⟨x, hx, hy⟩
  modal_K _ _
    (nec% (fun (h : ∀ x, R x → ∀ y, F x y → Z y) (y : τ)
      (hy : IndexedUnion R F y) => hy.elim fun x hx => h x hx.1 y hx.2)) hall

/-- A rigid index set of rigid fibers has a rigid union; current fiber rigidity suffices. -/
theorem indexed_union_rigid (R : σ → Prop) (F : σ → τ → Prop) (hR : Rigid R)
    (hF : ∀ x, R x → Rigid (F x)) : Rigid (IndexedUnion R F) :=
  have hf := rigid_family_sealed R F hR hF
  have hwp : □ (∀ x, R x → WeaklyPersistent (F x)) :=
    modal_K _ _ (nec% (fun (h : ∀ x, R x → Rigid (F x)) (x : σ) (hx : R x) =>
      weaklyPersistent_of_persistent (h x hx).1)) hf
  have hwi : □ (∀ x, R x → WeaklyInextensible (F x)) :=
    modal_K _ _ (nec% (fun (h : ∀ x, R x → Rigid (F x)) (x : σ) (hx : R x) =>
      weaklyInextensible_of_inextensible (h x hx).2)) hf
  ⟨modal_K _ _ (modal_K _ _ (nec% (indexed_union_weakly_persistent R F)) hR.1) hwp,
    modal_K _ _ (modal_K _ _ (nec% (indexed_union_weakly_inextensible R F)) hR.2) hwi⟩

theorem singleton_rigid (a : τ) : Rigid (fun y : τ => y = a) :=
  ⟨nec% (fun (y : τ) (hy : y = a) => necessity_of_identity y a hy),
    nec% (fun (Z : τ → Prop) (hZ : ∀ y : τ, y = a → □ (Z y)) =>
      modal_K _ _ (nec% (fun (hz : Z a) (y : τ) (hy : y = a) => hy.symm ▸ hz))
        (hZ a rfl))⟩

end indexedUnion

section maps
variable {σ τ : Type} [Ty σ] [Rel τ]

def DirectImage (f : σ → τ) (R : σ → Prop) : τ → Prop :=
  IndexedUnion R (fun x y => y = f x)
def Range (f : σ → τ) (y : τ) : Prop := ∃ x, y = f x
def InverseImage (f : σ → τ) (P : τ → Prop) : σ → Prop := fun x => P (f x)
def Injective (f : σ → τ) : Prop := ∀ x y : σ, f x = f y → x = y
def FiberGuard (f : σ → τ) (y : τ) (Z : σ → Prop) : Prop :=
  ∀ x : σ, y = f x → Z x

/-- Every admitted operation preserves rigid sets under direct image. -/
theorem direct_image_rigid (f : σ → τ) (R : σ → Prop) (hR : Rigid R) :
    Rigid (DirectImage f R) :=
  indexed_union_rigid R (fun x y => y = f x) hR fun x _ => singleton_rigid (f x)

theorem range_necessary (f : σ → τ) (y : τ) (hy : Range f y) : □ (Range f y) :=
  hy.elim fun x hx => modal_K _ _
    (nec% (fun (he : y = f x) => (show Range f y from ⟨x, he⟩)))
    (necessity_of_identity y (f x) hx)

theorem rigid_range_sealed (f : σ → τ) (P : τ → Prop) (hP : Rigid P)
    (hr : ∀ y, P y → Range f y) : □ (∀ y, P y → Range f y) :=
  weaklyInextensible_of_inextensible hP.2 (Range f)
    fun y hy => range_necessary f y (hr y hy)

theorem inverse_image_persistent (f : σ → τ) (P : τ → Prop) (hP : Persistent P) :
    Persistent (InverseImage f P) :=
  modal_K _ _ (nec% (fun (h : WeaklyPersistent P) (x : σ)
    (hx : InverseImage f P x) => h (f x) hx)) hP

theorem fiber_guard_of_injective (f : σ → τ) (y : τ) (a : σ) (Z : σ → Prop)
    (hi : Injective f) (hy : y = f a) (hz : Z a) : FiberGuard f y Z :=
  fun x hx => (hi x a (hx.symm.trans hy)).symm ▸ hz

theorem inverse_image_weakly_inextensible (f : σ → τ) (P : τ → Prop)
    (hP : WeaklyInextensible P) (hr : ∀ y, P y → Range f y)
    (hi : □ (Injective f)) : WeaklyInextensible (InverseImage f P) := fun Z hZ =>
  have hguards : □ (∀ y, P y → FiberGuard f y Z) :=
    hP (fun y => FiberGuard f y Z) fun y hy =>
      (hr y hy).elim fun a ha =>
        modal_K _ _ (modal_K _ _ (modal_K _ _
          (nec% (fiber_guard_of_injective f y a Z)) hi)
          (necessity_of_identity y (f a) ha)) (hZ a (Eq.mp (congrArg P ha) hy))
  modal_K _ _
    (nec% (fun (h : ∀ y, P y → FiberGuard f y Z) (x : σ)
      (hx : InverseImage f P x) => h (f x) hx x rfl)) hguards

/-- Both the range restriction and injectivity retain their modal scopes. -/
theorem inverse_image_rigid (f : σ → τ) (P : τ → Prop) (hP : Rigid P)
    (hr : ∀ y, P y → Range f y) (hi : □ (Injective f)) : Rigid (InverseImage f P) :=
  ⟨inverse_image_persistent f P hP.1,
    modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (inverse_image_weakly_inextensible f P)) hP.2)
      (rigid_range_sealed f P hP hr)) (modal_four _ hi)⟩

theorem direct_image_inverse_value (f : σ → τ) (X : σ → Prop) (hi : Injective f)
    (x : σ) : DirectImage f X (f x) ↔ X x :=
  ⟨fun h => h.elim fun a ha => (hi x a ha.2).symm ▸ ha.1,
    fun hx => ⟨x, hx, rfl⟩⟩

/-- Comprehension descends along a necessarily injective admitted operation. -/
theorem rigid_comprehension_descent (f : σ → τ) (hi : □ (Injective f))
    (rc : RigidComprehension (τ → Prop)) : RigidComprehension (σ → Prop) := fun X =>
  (rc (DirectImage f X)).elim fun P hP =>
    ⟨InverseImage f P,
      inverse_image_rigid f P hP.1
        (fun y hy => ((hP.2 y).2 hy).elim fun x hx => ⟨x, hx.2⟩) hi,
      fun x => ⟨fun hx => (hP.2 (f x)).1
        ((direct_image_inverse_value f X (box_elim hi) x).2 hx),
        fun hx => (direct_image_inverse_value f X (box_elim hi) x).1
          ((hP.2 (f x)).2 hx)⟩⟩

end maps

end Classicism.Research.ModalRigidityDescent

#classicism_check
  Classicism.Research.ModalRigidityDescent.rigid_necessary
  Classicism.Research.ModalRigidityDescent.rigid_family_sealed
  Classicism.Research.ModalRigidityDescent.indexed_union_weakly_persistent
  Classicism.Research.ModalRigidityDescent.indexed_union_weakly_inextensible
  Classicism.Research.ModalRigidityDescent.indexed_union_rigid
  Classicism.Research.ModalRigidityDescent.singleton_rigid
  Classicism.Research.ModalRigidityDescent.direct_image_rigid
  Classicism.Research.ModalRigidityDescent.range_necessary
  Classicism.Research.ModalRigidityDescent.rigid_range_sealed
  Classicism.Research.ModalRigidityDescent.inverse_image_persistent
  Classicism.Research.ModalRigidityDescent.fiber_guard_of_injective
  Classicism.Research.ModalRigidityDescent.inverse_image_weakly_inextensible
  Classicism.Research.ModalRigidityDescent.inverse_image_rigid
  Classicism.Research.ModalRigidityDescent.direct_image_inverse_value
  Classicism.Research.ModalRigidityDescent.rigid_comprehension_descent
#classicism_types
  Classicism.Research.ModalRigidityDescent.rigid_necessary
  Classicism.Research.ModalRigidityDescent.rigid_family_sealed
  Classicism.Research.ModalRigidityDescent.indexed_union_weakly_persistent
  Classicism.Research.ModalRigidityDescent.indexed_union_weakly_inextensible
  Classicism.Research.ModalRigidityDescent.indexed_union_rigid
  Classicism.Research.ModalRigidityDescent.singleton_rigid
  Classicism.Research.ModalRigidityDescent.direct_image_rigid
  Classicism.Research.ModalRigidityDescent.range_necessary
  Classicism.Research.ModalRigidityDescent.rigid_range_sealed
  Classicism.Research.ModalRigidityDescent.inverse_image_persistent
  Classicism.Research.ModalRigidityDescent.fiber_guard_of_injective
  Classicism.Research.ModalRigidityDescent.inverse_image_weakly_inextensible
  Classicism.Research.ModalRigidityDescent.inverse_image_rigid
  Classicism.Research.ModalRigidityDescent.direct_image_inverse_value
  Classicism.Research.ModalRigidityDescent.rigid_comprehension_descent
