import Classicism.Principles.Lattice
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem

/-!
Goodsell's singleton-supremum argument (Arithmetic is Necessary, 2024,
Lemma 8), factored through an arbitrary seed and successor at a relational type.
Formalization: OpenAI Codex, prompted by Andrew Bacon, 28 October 2026.

The completeness premise is local and explicit. It yields WeaklyRigid.
Its necessitation yields Rigid, whose definition has leading boxes.
No Infinity, Peano injectivity, choice, RC, BF, or ND premise is used.
-/
namespace Classicism.Numerical
open Classicism.Paper

/-- Boolean completeness in its greatest-lower-bound formulation. -/
def BooleanCompleteAt (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ → Prop, ∃ y : τ, GLB y X

/-- The impredicative closure of a seed under a successor operation. -/
def InductiveClosure {ν : Type} [Rel ν] (z : ν) (s : ν → ν) : ν → Prop :=
  fun n => ∀ X : ν → Prop, (X z ∧ ∀ m, X m → X (s m)) → X n

/-- The family of singleton properties of members of A. -/
def SingletonFamily {ν : Type} [Ty ν] (A : ν → Prop) : (ν → Prop) → Prop :=
  fun X => ∃ n, A n ∧ X = (fun m => n = m)

section closure
variable {ν : Type} [Rel ν] (z : ν) (s : ν → ν)

theorem inductiveClosure_zero : InductiveClosure z s z := fun _ h => h.1

theorem inductiveClosure_suc (n : ν) (hn : InductiveClosure z s n) :
    InductiveClosure z s (s n) := fun X h => h.2 n (hn X h)

theorem inductiveClosure_induction (X : ν → Prop)
    (hz : X z) (hs : ∀ n, X n → X (s n)) :
    ∀ n, InductiveClosure z s n → X n := fun n hn => hn X ⟨hz, hs⟩

/-- Goodsell Lemma 3, without any completeness assumption. -/
theorem inductiveClosure_box (n : ν) (hn : InductiveClosure z s n) :
    □ (InductiveClosure z s n) :=
  hn (fun m => □ (InductiveClosure z s m))
    ⟨nec% (inductiveClosure_zero z s),
      fun m hm => modal_K _ _ (nec% (inductiveClosure_suc z s m)) hm⟩

theorem inductiveClosure_persistent : Persistent (InductiveClosure z s) :=
  nec% (inductiveClosure_box z s)

end closure

section singletons
variable {ν : Type} [Ty ν]

theorem singleton_le_of_box (n : ν) (X : ν → Prop) (hx : □ (X n)) :
    (fun m => n = m) ≤ X :=
  (le_iff _ _).2 (modal_K _ _
    (nec% (fun (h : X n) (m : ν) (he : n = m) => he ▸ h)) hx)

theorem box_of_singleton_le (n : ν) (X : ν → Prop)
    (h : (fun m => n = m) ≤ X) : □ (X n) :=
  modal_K _ _ (nec% (fun (h : ∀ m, n = m → X m) => h n rfl))
    ((le_iff _ _).1 h)

theorem singletonFamily_upper (A X : ν → Prop)
    (h : ∀ n, A n → □ (X n)) : UB X (SingletonFamily A) := by
  intro Y hy
  obtain ⟨n, hn, he⟩ := hy
  exact he ▸ singleton_le_of_box n X (h n hn)

theorem singletonFamily_box (A B : ν → Prop) (hb : UB B (SingletonFamily A))
    (n : ν) (hn : A n) : □ (B n) :=
  box_of_singleton_le n B (hb (fun m => n = m) ⟨n, hn, rfl⟩)

/-- GLBs of upper bounds supply LUBs, using the existing lattice theorem. -/
theorem booleanCompleteAt_lub (bc : BooleanCompleteAt (ν → Prop))
    (F : (ν → Prop) → Prop) : ∃ B, LUB B F := by
  obtain ⟨B, hb⟩ := bc (fun Y => UB Y F)
  exact ⟨B, lub_of_glb_ubs F B hb⟩

end singletons

section rigidity
variable {ν : Type} [Rel ν] (z : ν) (s : ν → ν)

/-- The LUB of the singleton family is necessarily successor-closed. -/
theorem inductiveClosure_lub_step (B : ν → Prop)
    (hb : LUB B (SingletonFamily (InductiveClosure z s))) :
    □ (∀ n, B n → B (s n)) := by
  have hu : UB B (SingletonFamily (InductiveClosure z s)) :=
    (hb B).2 (le_refl_rel B)
  have hv : UB (fun n => B (s n)) (SingletonFamily (InductiveClosure z s)) :=
    singletonFamily_upper _ _ (fun n hn =>
      singletonFamily_box _ B hu (s n) (inductiveClosure_suc z s n hn))
  exact (le_iff _ _).1 ((hb (fun n => B (s n))).1 hv)

/-- Necessitated induction puts the whole inductive closure below the LUB. -/
theorem inductiveClosure_le_lub (B : ν → Prop)
    (hb : LUB B (SingletonFamily (InductiveClosure z s))) :
    InductiveClosure z s ≤ B := by
  have hu : UB B (SingletonFamily (InductiveClosure z s)) :=
    (hb B).2 (le_refl_rel B)
  have hz : □ (B z) :=
    singletonFamily_box _ B hu z (inductiveClosure_zero z s)
  exact (le_iff _ _).2 (modal_K _ _
    (modal_K _ _ (nec% (inductiveClosure_induction z s B)) hz)
    (inductiveClosure_lub_step z s B hb))

/-- Goodsell Lemma 8: only existence of this one supremum is needed. -/
theorem inductiveClosure_restricted_barcan_of_lub (B : ν → Prop)
    (hb : LUB B (SingletonFamily (InductiveClosure z s)))
    (X : ν → Prop) (hx : ∀ n, InductiveClosure z s n → □ (X n)) :
    □ (∀ n, InductiveClosure z s n → X n) :=
  (le_iff _ _).1 (le_trans_rel _ B X (inductiveClosure_le_lub z s B hb)
    ((hb X).1 (singletonFamily_upper _ X hx)))

theorem inductiveClosure_weaklyInextensible
    (bc : BooleanCompleteAt (ν → Prop)) :
    WeaklyInextensible (InductiveClosure z s) := by
  obtain ⟨B, hb⟩ := booleanCompleteAt_lub bc (SingletonFamily (InductiveClosure z s))
  exact inductiveClosure_restricted_barcan_of_lub z s B hb

theorem inductiveClosure_weaklyRigid
    (bc : BooleanCompleteAt (ν → Prop)) : WeaklyRigid (InductiveClosure z s) :=
  ⟨inductiveClosure_box z s, inductiveClosure_weaklyInextensible z s bc⟩

/-- Strong rigidity in the map's convention, from necessary completeness. -/
theorem inductiveClosure_rigid
    (bc : □ (BooleanCompleteAt (ν → Prop))) : Rigid (InductiveClosure z s) :=
  ⟨inductiveClosure_persistent z s,
    modal_K _ _ (nec% (inductiveClosure_weaklyInextensible z s)) bc⟩

end rigidity

#classicism_check inductiveClosure_zero inductiveClosure_suc inductiveClosure_induction
  inductiveClosure_box inductiveClosure_persistent singleton_le_of_box box_of_singleton_le
  singletonFamily_upper singletonFamily_box booleanCompleteAt_lub inductiveClosure_lub_step
  inductiveClosure_le_lub inductiveClosure_restricted_barcan_of_lub
  inductiveClosure_weaklyInextensible inductiveClosure_weaklyRigid inductiveClosure_rigid
#classicism_types inductiveClosure_zero inductiveClosure_suc inductiveClosure_induction
  inductiveClosure_box inductiveClosure_persistent singleton_le_of_box box_of_singleton_le
  singletonFamily_upper singletonFamily_box booleanCompleteAt_lub inductiveClosure_lub_step
  inductiveClosure_le_lub inductiveClosure_restricted_barcan_of_lub
  inductiveClosure_weaklyInextensible inductiveClosure_weaklyRigid inductiveClosure_rigid

end Classicism.Numerical
