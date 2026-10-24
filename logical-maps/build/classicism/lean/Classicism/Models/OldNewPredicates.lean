import Classicism.Models.OldNewND

/-!
# Admitted old/new unary witnesses

Original formalization (misc), 22 October 2026, of the explicit witnesses in
old-new-boolean-completeness-and-rigidity-separation.md (IC and future BC).
Every witness is proved admitted by finite pinning and target symmetry.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory
noncomputable section

abbrev et : RTy := .arr .e .t

theorem mem_at {W : cat.Ob} {ρ : RTy} (F : Intension model.inner ρ W)
    (h : (∃ S : Set (X W), S.Finite ∧ ∀ V (f g : W ⟶ V), AgreeOn cat.De S f g →
      Intension.map model.inner f F = Intension.map model.inner g F) ∧ model.Sym syms F) :
    F ∈ Set.range (model.incl ρ W) :=
  (mem_range_symIncl cat.De syms (PinIdeal.fin cat.De) ρ W F).2 h

def oldRaw (W : cat.Ob) : Intension model.inner et W := fun p => old p.1 p.2.1.1

theorem oldRaw_mem (W : cat.Ob) : oldRaw W ∈ Set.range (model.incl et W) := by
  apply mem_at
  refine ⟨⟨∅, Set.finite_empty, fun V f g _ => ?_⟩, ?_⟩
  · ext p; rfl
  · intro V a k g hg ha
    exact (hg.2 a.1).2 ha

def oldEntity (W : cat.Ob) : RelDom W et := Classical.choose (oldRaw_mem W)

theorem incl_old (W : cat.Ob) : model.incl et W (oldEntity W) = oldRaw W :=
  Classical.choose_spec (oldRaw_mem W)

def topRaw (W : cat.Ob) : Intension model.inner et W := Set.univ

theorem topRaw_mem (W : cat.Ob) : topRaw W ∈ Set.range (model.incl et W) := by
  apply mem_at
  exact ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩, fun _ _ _ _ _ _ => trivial⟩

def topEntity (W : cat.Ob) : RelDom W et := Classical.choose (topRaw_mem W)

theorem incl_top (W : cat.Ob) : model.incl et W (topEntity W) = topRaw W :=
  Classical.choose_spec (topRaw_mem W)

def pointRaw (W : cat.Ob) (x : X W) : Intension model.inner et W :=
  fun p => p.2.1.1 = FunCat.fn p.2.2 x

def avoidRaw (W : cat.Ob) (x : X W) : Intension model.inner et W :=
  fun p => p.2.1.1 ≠ FunCat.fn p.2.2 x

theorem pointRaw_mem (W : cat.Ob) (x : X W) : pointRaw W x ∈ Set.range (model.incl et W) := by
  apply mem_at
  refine ⟨⟨{x}, Set.finite_singleton x, ?_⟩, ?_⟩
  · intro V f g ha
    ext ⟨U, a, k⟩
    change (a.1 = FunCat.fn k (FunCat.fn f x)) ↔ (a.1 = FunCat.fn k (FunCat.fn g x))
    exact Iff.of_eq (congrArg (fun y : X V => (a.1 : X U) = FunCat.fn k y)
      (ha x (Set.mem_singleton x)))
  · intro V a k g hg ha
    change FunCat.fn g a.1 = FunCat.fn g (FunCat.fn k x)
    exact congrArg (FunCat.fn g) ha

theorem avoidRaw_mem (W : cat.Ob) (x : X W) : avoidRaw W x ∈ Set.range (model.incl et W) := by
  apply mem_at
  refine ⟨⟨{x}, Set.finite_singleton x, ?_⟩, ?_⟩
  · intro V f g ha
    ext ⟨U, a, k⟩
    change (a.1 ≠ FunCat.fn k (FunCat.fn f x)) ↔ (a.1 ≠ FunCat.fn k (FunCat.fn g x))
    exact Iff.of_eq (congrArg (fun y : X V => (a.1 : X U) ≠ FunCat.fn k y)
      (ha x (Set.mem_singleton x)))
  · intro V a k g hg ha
    change FunCat.fn g a.1 ≠ FunCat.fn g (FunCat.fn k x)
    exact fun e => ha (g.2.1 e)

def pointEntity (W : cat.Ob) (x : X W) : RelDom W et := Classical.choose (pointRaw_mem W x)
def avoidEntity (W : cat.Ob) (x : X W) : RelDom W et := Classical.choose (avoidRaw_mem W x)

theorem incl_point (W : cat.Ob) (x : X W) : model.incl et W (pointEntity W x) = pointRaw W x :=
  Classical.choose_spec (pointRaw_mem W x)

theorem incl_avoid (W : cat.Ob) (x : X W) : model.incl et W (avoidEntity W x) = avoidRaw W x :=
  Classical.choose_spec (avoidRaw_mem W x)

@[simp] theorem profile_old {W V : cat.Ob} (h : W ⟶ V) (a : Tup et V) :
    profile (oldEntity W) h a ↔ old V a.1 := by
  unfold profile
  rw [incl_old]
  rfl

@[simp] theorem profile_top {W V : cat.Ob} (h : W ⟶ V) (a : Tup et V) :
    profile (topEntity W) h a := by
  unfold profile
  rw [incl_top]
  trivial

@[simp] theorem profile_point {W V : cat.Ob} (x : X W) (h : W ⟶ V) (a : Tup et V) :
    profile (pointEntity W x) h a ↔ a.1 = FunCat.fn h x := by
  unfold profile
  rw [incl_point]
  rfl

@[simp] theorem profile_avoid {W V : cat.Ob} (x : X W) (h : W ⟶ V) (a : Tup et V) :
    profile (avoidEntity W x) h a ↔ a.1 ≠ FunCat.fn h x := by
  unfold profile
  rw [incl_avoid]
  rfl

theorem avoid_map {W V : cat.Ob} (k : W ⟶ V) (x : X W) :
    (model.inner (.rel et)).map k (avoidEntity W x) = avoidEntity V (FunCat.fn k x) := by
  apply model.Incl_injective (.rel et) V
  change model.incl et V _ = model.incl et V _
  rw [model.incl_map, incl_avoid, incl_avoid]
  rfl

/-- A genuine represented family: the complements of the old haecceities.
Its GLB failure is the Boolean dual of the corrected old-haecceity LUB failure. -/
def oldAvoidRaw (W : cat.Ob) : Intension model.inner (.arr (.rel et) .t) W :=
  fun p => ∃ x : X p.1, old p.1 x ∧ p.2.1.1 = avoidEntity p.1 x

theorem oldAvoidRaw_mem (W : cat.Ob) :
    oldAvoidRaw W ∈ Set.range (model.incl (.arr (.rel et) .t) W) := by
  apply mem_at
  refine ⟨⟨∅, Set.finite_empty, fun _ _ _ _ => rfl⟩, ?_⟩
  intro V a k g hg
  rintro ⟨x, hx, he⟩
  refine ⟨FunCat.fn g x, (hg.2 x).2 hx, ?_⟩
  change (model.inner (.rel et)).map g a.1 = avoidEntity V (FunCat.fn g x)
  rw [he, avoid_map]

def oldAvoidFamily (W : cat.Ob) : RelDom W (.arr (.rel et) .t) :=
  Classical.choose (oldAvoidRaw_mem W)

theorem incl_oldAvoid (W : cat.Ob) :
    model.incl (.arr (.rel et) .t) W (oldAvoidFamily W) = oldAvoidRaw W :=
  Classical.choose_spec (oldAvoidRaw_mem W)

theorem point_below_avoid {W : cat.Ob} {x y : X W} (hne : x ≠ y) :
    model.incl et W (pointEntity W x) ⊆ model.incl et W (avoidEntity W y) := by
  rintro ⟨V, a, k⟩ ha
  change profile (pointEntity W x) k a at ha
  change profile (avoidEntity W y) k a
  rw [profile_point] at ha
  rw [profile_avoid, ha]
  exact fun e => hne (k.2.1 e)

theorem pinned_profile_at {W : cat.Ob} {ρ : RTy} {F : RelDom W ρ} {S : Set (X W)}
    (hp : model.PinnedO (.rel ρ) (W := W) S (model.incl ρ W F))
    {V : cat.Ob} {h i : W ⟶ V} (ha : AgreeOn cat.De S h i) (a : Tup ρ V) :
    profile F h a ↔ profile F i a := by
  have he := congrArg (fun R : Intension model.inner ρ V =>
    (⟨V, a, 𝟙 V⟩ : Tuple model.inner ρ V) ∈ R) (hp V h i ha)
  simpa only [Outer.map_rel, Intension.mem_map, Category.comp_id, profile] using Iff.of_eq he

end
end Classicism.Meta.Intensional.OldNew
