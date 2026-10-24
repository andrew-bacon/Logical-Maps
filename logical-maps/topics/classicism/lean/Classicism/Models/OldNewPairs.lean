import Classicism.Models.OldNewBase

/-!
# Invariant profile pairs and Boolean Completeness at E

Original proof (misc): research/2026-10-22/notes/
old-new-boolean-completeness-and-rigidity-separation.md, section Full Boolean
Completeness at E (unpaginated). We construct a new admitted intension from
its two invariant profiles. We do not take the pointwise intersection or
union of the current family's full intensions.

The recursion over relation types is already in Args and the model's actions;
all arguments below quantify over an arbitrary RTy, including t.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory
noncomputable section

abbrev RelDom (W : cat.Ob) (ρ : RTy) := model.Dom W (.rel ρ)
abbrev Tup (ρ : RTy) (V : cat.Ob) := Args model.inner ρ V

def profile {ρ : RTy} {W V : cat.Ob} (F : RelDom W ρ) (h : W ⟶ V) (a : Tup ρ V) : Prop :=
  (⟨V, a, h⟩ : Tuple model.inner ρ W) ∈ model.incl ρ W F

def component {ρ : RTy} (F : RelDom E ρ) (V : cat.Ob) : Set (Tup ρ V) :=
  fun a => profile F (canon V) a

abbrev PairData (ρ : RTy) := ∀ V : cat.Ob, Set (Tup ρ V)

def Invariant {ρ : RTy} (S : Set Nat) (P : PairData ρ) : Prop :=
  ∀ V (g : V ⟶ V), g ∈ syms V →
    (∀ x ∈ S, FunCat.fn g (canonFn V x) = canonFn V x) →
      ∀ a, P V a → P V (Args.map model.inner ρ g a)

def rebuild {ρ : RTy} (S : Set Nat) (P : PairData ρ) : Intension model.inner ρ E :=
  fun t => ∃ g ∈ syms t.1, AgreeOn cat.De S t.2.2 (canon t.1 ≫ g) ∧
    ∃ a, P t.1 a ∧ Args.map model.inner ρ g a = t.2.1

/-- Admission is proved directly from the literal symmetric/pinned conditions. -/
theorem rebuild_mem {ρ : RTy} {S : Set Nat} (hS : S.Finite) (P : PairData ρ) :
    rebuild S P ∈ Set.range (model.incl ρ E) := by
  apply (SymBase.mem_range_iff (S := base) ρ (rebuild S P)).2
  refine ⟨⟨S, hS, ?_⟩, ?_⟩
  · intro V h i ha
    ext ⟨U, a, k⟩
    constructor
    · rintro ⟨g, hg, hag, b, hb, he⟩
      exact ⟨g, hg, ((ha.comp_right cat.De k).symm cat.De).trans cat.De hag, b, hb, he⟩
    · rintro ⟨g, hg, hag, b, hb, he⟩
      exact ⟨g, hg, (ha.comp_right cat.De k).trans cat.De hag, b, hb, he⟩
  · intro V a k s hs
    rintro ⟨g, hg, hag, b, hb, he⟩
    refine ⟨g ≫ s, base.G_comp hg hs, ?_, b, hb, ?_⟩
    · simpa only [Category.assoc] using hag.comp_right cat.De s
    · rw [Args.map_comp, he]
      rfl

theorem rebuild_component {ρ : RTy} {S : Set Nat} {P : PairData ρ}
    (hP : Invariant S P) (V : cat.Ob) (a : Tup ρ V) :
    (⟨V, a, canon V⟩ : Tuple model.inner ρ E) ∈ rebuild S P ↔ P V a := by
  constructor
  · rintro ⟨g, hg, hag, b, hb, he⟩
    exact Eq.mp (congrArg (P V) he)
      (hP V g hg (fun x hx => (hag x hx).symm) b hb)
  · intro ha
    exact ⟨𝟙 V, base.G_id V, fun _ _ => rfl, a, ha, Args.map_id _ _ _ _⟩

theorem profile_agree {ρ : RTy} {F : RelDom E ρ} {S : Set Nat}
    (hp : model.PinnedO (.rel ρ) (W := E) S (model.incl ρ E F))
    {V : cat.Ob} {h i : E ⟶ V} (ha : AgreeOn cat.De S h i) (a : Tup ρ V) :
    profile F h a ↔ profile F i a :=
  ⟨SymBase.mem_of_pinned (S := base) hp ha a,
    SymBase.mem_of_pinned (S := base) hp (ha.symm cat.De) a⟩

theorem profile_approx {ρ : RTy} {F : RelDom E ρ} {S : Set Nat}
    (hp : model.PinnedO (.rel ρ) (W := E) S (model.incl ρ E F))
    {V : cat.Ob} {h : E ⟶ V} {g gi : V ⟶ V} (hg : g ∈ syms V)
    (hgi : gi ≫ g = 𝟙 V) (ha : AgreeOn cat.De S h (canon V ≫ g)) (a : Tup ρ V) :
    profile F h a ↔ component F V (Args.map model.inner ρ gi a) := by
  have hs := Premodel.Sym.iff (B := model) syms_inv
    (SymBase.model_domSym (S := base) ρ E F)
    (Args.map model.inner ρ gi a) (canon V) hg
  rw [Premodel.args_map_map_inv (B := model) hgi a] at hs
  exact (profile_agree hp ha a).trans hs

/-- Order is exactly componentwise inclusion. The same extending symmetry
is used for the two finite supports. -/
theorem subset_iff_components {ρ : RTy} (F G : RelDom E ρ) :
    model.incl ρ E F ⊆ model.incl ρ E G ↔
      ∀ V, component F V ⊆ component G V := by
  constructor
  · intro h V a ha; exact h ha
  · intro hc
    obtain ⟨SF, hSF, hpF⟩ := SymBase.finPinned (S := base) (.rel ρ) F
    obtain ⟨SG, hSG, hpG⟩ := SymBase.finPinned (S := base) (.rel ρ) G
    rintro ⟨V, a, h⟩ ha
    obtain ⟨g, hg, hag⟩ := approximate h (hSF.union hSG)
    obtain ⟨gi, _, _, hgi⟩ := syms_inv V g hg
    have eF := profile_approx hpF hg hgi (fun x hx => hag x (Or.inl hx)) a
    have eG := profile_approx hpG hg hgi (fun x hx => hag x (Or.inr hx)) a
    exact eG.2 (hc V (eF.1 ha))

/-- The advertised action on profile pairs, with the actual higher-type
tuple action. A target symmetry factors through the root canonical arrow. -/
theorem component_map {ρ : RTy} (F : RelDom E ρ) {V : cat.Ob}
    {s : E ⟶ E} {g : V ⟶ V} (hg : g ∈ syms V)
    (he : canon V ≫ g = s ≫ canon V) (a : Tup ρ V) :
    component ((model.inner (.rel ρ)).map s F) V (Args.map model.inner ρ g a) ↔
      component F V a := by
  unfold component profile
  rw [model.incl_map]
  change (⟨V, Args.map model.inner ρ g a, s ≫ canon V⟩ : Tuple model.inner ρ E) ∈
    model.incl ρ E F ↔ _
  rw [← he]
  exact Premodel.Sym.iff (B := model) syms_inv
    (SymBase.model_domSym (S := base) ρ E F) a (canon V) hg

def family {ρ : RTy} (F : RelDom E (.arr (.rel ρ) .t)) (A : RelDom E ρ) : Prop :=
  profile F (𝟙 E) (A, PUnit.unit)

def intersectionPair {ρ : RTy} (F : RelDom E (.arr (.rel ρ) .t)) : PairData ρ :=
  fun V a => ∀ A, family F A → component A V a

/-- Intersections of the invariant profiles of a represented family are
invariant under the finite stabilizer of that family. -/
theorem intersection_invariant {ρ : RTy} (F : RelDom E (.arr (.rel ρ) .t))
    {S : Set Nat} (hp : model.PinnedO (.rel (.arr (.rel ρ) .t)) (W := E) S (model.incl _ E F)) :
    Invariant S (intersectionPair F) := by
  intro V g hg hfix a ha A hA
  obtain ⟨s, hs, hfactor⟩ := factor_sym g hg
  have hsfix : ∀ x ∈ S, FunCat.fn s x = x := by
    intro x hx
    apply canon_injective V
    have he := congrFun (congrArg (fun k : E ⟶ V => FunCat.fn k) hfactor) x
    exact he.symm.trans (hfix x hx)
  obtain ⟨si, hsi, _, hsi_s⟩ := syms_inv E s hs
  have hsifix : ∀ x ∈ S, FunCat.fn si x = x := by
    intro x hx
    apply hs.1.1
    have he := congrFun (congrArg (fun k : E ⟶ E => FunCat.fn k) hsi_s) x
    exact he.trans (hsfix x hx).symm
  let A' := (model.inner (.rel ρ)).map si A
  have hA' : family F A' :=
    SymBase.orbit_ext (S := base) hp hsi hsifix hA
  have hcomp := (component_map A' hg hfactor a).2 (ha A' hA')
  change component ((model.inner (.rel ρ)).map s ((model.inner (.rel ρ)).map si A)) V
    (Args.map model.inner ρ g a) at hcomp
  rw [Premodel.map_map_inv (B := model) hsi_s A] at hcomp
  exact hcomp

/-- Every represented family has a greatest lower bound, constructed by
intersecting its two profiles and then rebuilding an admitted intension. -/
theorem root_glbs (ρ : RTy) (F : RelDom E (.arr (.rel ρ) .t)) :
    ∃ y : RelDom E ρ, ∀ z : RelDom E ρ,
      (∀ A : RelDom E ρ, family F A → model.incl ρ E z ⊆ model.incl ρ E A) ↔
        model.incl ρ E z ⊆ model.incl ρ E y := by
  obtain ⟨S, hS, hp⟩ := SymBase.finPinned (S := base) (.rel _) F
  obtain ⟨y, hy⟩ := rebuild_mem hS (intersectionPair F)
  have hpair : ∀ V a, component y V a ↔ intersectionPair F V a := by
    intro V a
    change (⟨V, a, canon V⟩ : Tuple model.inner ρ E) ∈ model.incl ρ E y ↔ _
    rw [hy]
    exact rebuild_component (intersection_invariant F hp) V a
  refine ⟨y, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    apply (subset_iff_components z y).2
    intro V a ha
    apply (hpair V a).2
    intro A hA
    exact (subset_iff_components z A).1 (hz A hA) V ha
  · intro hz A hA
    apply (subset_iff_components z A).2
    intro V a ha
    exact (hpair V a).1 ((subset_iff_components z y).1 hz V ha) A hA

/-- The official all-relational-type BC instance at the original root.
It is deliberately not boxed and is not asserted at O. -/
theorem root_bc (ρ : RTy) : model.HoldsSentence (P.BooleanCompleteness.quoted ρ) := by
  exact (model.holds_bc_iff isModel ρ (𝟙 E)).2 (root_glbs ρ)

end
end Classicism.Meta.Intensional.OldNew
