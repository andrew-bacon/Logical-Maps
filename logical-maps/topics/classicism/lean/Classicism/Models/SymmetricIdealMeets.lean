import Classicism.Models.SymmetricIdeal
import Classicism.Models.SymTransposable
import Classicism.Models.OldNewBase
import Classicism.Models.FiniteCompressionBase

/-!
# More members of `symmetric-ideally-full`, and more of the members' conditions

- `classReflect`: the class-reflecting surjections of infinitely many infinite classes
  (`models/symmetric-class-reflecting-surjections.yaml`, Cian Dorr with Claude Opus 5.5,
  16 October 2026): over `ℕ`, the classes `cls n`, the first coordinate of `Nat.unpair n`;
  the arrows the surjections that reflect the classes (they identify two points only within
  a class), the symmetries the permutations preserving the classes. Its conditions
  `transposable` (a transposition within a class, as for `infClasses`), `surjective-arrows`
  and infinitely many individuals.
- The conditions `transposable`, `infinitely-many-individuals` and `separable-collapses` of
  members whose Lean base was already here but whose records gave no Lean proof of them: the
  qualitative contrast (`contrastBase`), the two-object model with its second object unpinned
  (`twoBase`), the old/new individuals (`OldNew.base`) and the finite-compression entrance
  (`FiniteCompression.base A`). Each has every permutation of the base object's individuals
  among its symmetries there, so `transposable` is `SymBase.transposable_of_moves'` with a
  transposition. Original formalization (`misc`), 3 November 2026.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace SymIdeal

/-! ### Fresh points and transpositions -/

/-- A finite set of an infinite type has a point outside it and outside another given point. -/
theorem exists_fresh_of_infinite {α : Type} [Infinite α] {K : Set α} (hK : K.Finite) (y : α) :
    ∃ z ∉ K, z ≠ y := by
  obtain ⟨z, hz⟩ := (hK.union (Set.finite_singleton y)).exists_notMem
  exact ⟨z, fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩

theorem swap_fix' {α : Type} [DecidableEq α] {y z a : α} {K : Set α} (hy : y ∉ K) (hz : z ∉ K)
    (ha : a ∈ K) : Equiv.swap y z a = a :=
  Equiv.swap_apply_of_ne_of_ne (fun e => hy (e ▸ ha)) (fun e => hz (e ▸ ha))

/-- **`transposable`** for a base whose individuals at the base object form an infinite type
and whose symmetries there include every transposition. -/
theorem transposable_of_swaps (S : SymBase) [Infinite (S.F.X S.W₀)] [DecidableEq (S.F.X S.W₀)]
    (hswap : ∀ y z : S.F.X S.W₀, ∃ g ∈ S.G S.W₀, FunCat.fn g = Equiv.swap y z) :
    S.Transposable :=
  SymBase.transposable_of_moves' (fun _ hK => hK.exists_notMem) fun K hK y hy => by
    obtain ⟨z, hz, hzy⟩ := exists_fresh_of_infinite hK y
    obtain ⟨g, hg, hfn⟩ := hswap y z
    refine ⟨g, hg, fun x hx => ?_, ?_⟩
    · rw [hfn]; exact swap_fix' hy hz hx
    · rw [hfn, Equiv.swap_apply_left]; exact hzy

/-- The map sending `2i + 1` to `2i` and fixing every other point. -/
def twoCollapse (i : ℕ) (x : ℕ) : ℕ := if x = 2 * i + 1 then 2 * i else x

/-! ### The class-reflecting surjections -/

/-- That `f` reflects the classes: it identifies two points only within a class. -/
def ReflectsCls (f : ℕ → ℕ) : Prop := ∀ x y, cls (f x) = cls (f y) → cls x = cls y

/-- The class-reflecting surjections of infinitely many infinite classes; the permutations
preserving the classes. -/
def classReflect : Base where
  Arr f := Function.Surjective f ∧ ReflectsCls f
  arr_id := ⟨Function.surjective_id, fun _ _ h => h⟩
  arr_comp hf hg := ⟨hg.1.comp hf.1, fun x y h => hf.2 x y (hg.2 _ _ h)⟩
  Sym f := Function.Bijective f ∧ ∀ x y, cls (f x) = cls (f y) ↔ cls x = cls y
  sym_arr h := ⟨h.1.2, fun x y => (h.2 x y).1⟩
  sym_bij h := h.1
  sym_inv {f} h := by
    refine ⟨(Equiv.ofBijective f h.1).symm.bijective, fun x y => ?_⟩
    have := h.2 ((Equiv.ofBijective f h.1).symm x) ((Equiv.ofBijective f h.1).symm y)
    rw [Equiv.ofBijective_apply_symm_apply f h.1 x, Equiv.ofBijective_apply_symm_apply f h.1 y] at this
    exact this.symm
  sym_id := ⟨Function.bijective_id, fun _ _ => Iff.rfl⟩
  sym_comp hf hg := ⟨hg.1.comp hf.1, fun x y => (hg.2 _ _).trans (hf.2 x y)⟩

theorem classReflect_transposable : classReflect.toSym.Transposable :=
  transposable_of ∅ Set.finite_empty fun K hK _ y _ => by
    have hfin : {m | Nat.pair (cls y) m ∈ K ∪ {y}}.Finite :=
      (hK.union (Set.finite_singleton y)).preimage
        (fun a _ b _ e => (Nat.pair_eq_pair.1 e).2)
    obtain ⟨m, hm⟩ := hfin.exists_notMem
    have hc : cls y = cls (Nat.pair (cls y) m) := by simp [cls, Nat.unpair_pair]
    refine ⟨Nat.pair (cls y) m, fun h => hm (Or.inl h), fun h => hm (Or.inr h), (Equiv.swap _ _).bijective,
      fun a b => ?_⟩
    rw [cls_swap hc, cls_swap hc]

theorem classReflect_surjectiveArrows : classReflect.toSym.SurjectiveArrows := fun _ k => k.2.1

/-! ### The permutations of infinitely many infinite classes -/

/-- All permutations; the permutations preserving the classes. -/
def permInfClasses : Base where
  Arr f := Function.Bijective f
  arr_id := Function.bijective_id
  arr_comp hf hg := hg.comp hf
  Sym f := Function.Bijective f ∧ ∀ x y, cls (f x) = cls (f y) ↔ cls x = cls y
  sym_arr h := h.1
  sym_bij h := h.1
  sym_inv {f} h := by
    refine ⟨(Equiv.ofBijective f h.1).symm.bijective, fun x y => ?_⟩
    have := h.2 ((Equiv.ofBijective f h.1).symm x) ((Equiv.ofBijective f h.1).symm y)
    rw [Equiv.ofBijective_apply_symm_apply f h.1 x, Equiv.ofBijective_apply_symm_apply f h.1 y] at this
    exact this.symm
  sym_id := ⟨Function.bijective_id, fun _ _ => Iff.rfl⟩
  sym_comp hf hg := ⟨hg.1.comp hf.1, fun x y => (hg.2 _ _).trans (hf.2 x y)⟩

theorem permInfClasses_transposable : permInfClasses.toSym.Transposable :=
  transposable_of ∅ Set.finite_empty fun K hK _ y _ => by
    have hfin : {m | Nat.pair (cls y) m ∈ K ∪ {y}}.Finite :=
      (hK.union (Set.finite_singleton y)).preimage
        (fun a _ b _ e => (Nat.pair_eq_pair.1 e).2)
    obtain ⟨m, hm⟩ := hfin.exists_notMem
    have hc : cls y = cls (Nat.pair (cls y) m) := by simp [cls, Nat.unpair_pair]
    refine ⟨Nat.pair (cls y) m, fun h => hm (Or.inl h), fun h => hm (Or.inr h), (Equiv.swap _ _).bijective,
      fun a b => ?_⟩
    rw [cls_swap hc, cls_swap hc]

theorem permInfClasses_surjectiveArrows : permInfClasses.toSym.SurjectiveArrows := fun _ k => k.2.2

/-! ### Two objects, `ℕ` and a point, all maps -/

/-- `ℕ` at the first object, one point at the second, and every map between them. -/
def allMapsCat : FunCat where
  Obj := Bool
  X b := match b with
    | false => ℕ
    | true => Unit
  Arr _ := True
  arr_id _ := trivial
  arr_comp _ _ := trivial

/-- The symmetries: the permutations, at both objects. -/
def allMapsSyms (V : allMapsCat.Ob) : Set (V ⟶ V) := {g | Function.Bijective (FunCat.fn g)}

theorem allMapsSyms_symGroup : SymGroup allMapsSyms := by
  intro V g hg
  let e := Equiv.ofBijective _ hg
  refine ⟨FunCat.arr (F := allMapsCat) (i := V) (j := V) e.symm trivial, e.symm.bijective, ?_, ?_⟩
  · exact FunCat.hom_ext (funext fun x => e.symm_apply_apply x)
  · exact FunCat.hom_ext (funext fun x => e.apply_symm_apply x)

/-- The base, at the first object, with the finite sets at both. -/
def allMapsBase : SymBase where
  F := allMapsCat
  G := allMapsSyms
  G_id _ := Function.bijective_id
  G_comp hg hs := hs.comp hg
  G_inv := allMapsSyms_symGroup
  W₀ := (false : Bool)
  ne V := match V with
    | false => ⟨(0 : ℕ)⟩
    | true => ⟨()⟩
  J := PinIdeal.fin _
  J_base _ h := h

theorem allMaps_transposable : allMapsBase.Transposable := by
  haveI : Infinite (allMapsBase.F.X allMapsBase.W₀) := inferInstanceAs (Infinite ℕ)
  haveI : DecidableEq (allMapsBase.F.X allMapsBase.W₀) := inferInstanceAs (DecidableEq ℕ)
  exact transposable_of_swaps allMapsBase fun y z =>
    ⟨FunCat.arr (F := allMapsCat) (i := false) (j := false) (Equiv.swap y z) trivial,
      (Equiv.swap y z).bijective, rfl⟩

theorem allMaps_infinitelyManyIndividuals : allMapsBase.model.InfinitelyManyIndividuals :=
  inferInstanceAs (Infinite ℕ)

/-- Separable collapses, the pairs `2i, 2i + 1`: every map is an arrow. -/
theorem allMaps_separable : allMapsBase.SeparableCollapses := by
  refine ⟨fun i => (2 * i : ℕ), fun i => (2 * i + 1 : ℕ), fun i j hij => ?_⟩
  refine ⟨(false : Bool), FunCat.arr (F := allMapsCat) (i := false) (j := false) (twoCollapse i) trivial,
    Or.inl ⟨?_, ?_⟩⟩
  · show twoCollapse i (2 * i) = twoCollapse i (2 * i + 1)
    simp only [twoCollapse]; split_ifs <;> omega
  · show twoCollapse i (2 * j) ≠ twoCollapse i (2 * j + 1)
    simp only [twoCollapse]; split_ifs <;> omega

/-- **The hull conditions** with `M₀ = ∅`: every map is an arrow, so prescriptions agreeing on
`P ∩ Q` splice, and into the point there is one arrow; the permutations move points. -/
theorem allMaps_hullConditions : allMapsBase.HullConditions := by
  classical
  refine ⟨∅, Set.finite_empty, fun M _ _ V h _ h' hag P Q _ _ hPQ => ?_, fun N P Q hN hP hQ _ => ?_⟩
  · cases V with
    | false =>
      let j : ℕ → ℕ := fun x => if x ∈ P then FunCat.fn h' x else FunCat.fn h x
      refine ⟨FunCat.arr (F := allMapsCat) (i := false) (j := false) j trivial, fun x hx => ?_, fun x hx => ?_⟩
      · show j x = FunCat.fn h' x
        simp only [j, if_pos hx]
      · show j x = FunCat.fn h x
        simp only [j]
        split_ifs with hxP
        · exact (hag x (hPQ ⟨hxP, hx⟩)).symm
        · rfl
    | true => exact ⟨h, fun _ _ => rfl, fun _ _ => rfl⟩
  · obtain ⟨g, hg, hfix, hmove⟩ := move_points (B := allSurj) ∅
      (fun K hK y _ => by
        obtain ⟨z, hz, -⟩ := exists_fresh hK y
        exact ⟨z, hz, (Equiv.swap y z).bijective⟩)
      ((hP.diff (t := N)).toFinset) N Q hN hQ (Set.empty_subset _)
      fun s hs => ((Set.Finite.mem_toFinset _).1 hs).2
    exact ⟨FunCat.arr (F := allMapsCat) (i := false) (j := false) g trivial, hg, hfix,
      fun x hx hxN => hmove x ((Set.Finite.mem_toFinset _).2 ⟨hx, hxN⟩)⟩

/-! ### The qualitative contrast -/

theorem contrast_transposable : contrastBase.Transposable := by
  haveI : Infinite (contrastBase.F.X contrastBase.W₀) := inferInstanceAs (Infinite ℕ)
  haveI : DecidableEq (contrastBase.F.X contrastBase.W₀) := inferInstanceAs (DecidableEq ℕ)
  exact transposable_of_swaps contrastBase fun y z =>
    ⟨FunCat.arr (F := contrastCat) (i := W₀) (j := W₀) (Equiv.swap y z) (Equiv.swap y z).bijective,
      trivial, rfl⟩

/-! ### Two objects, the second unpinned -/

theorem two_transposable : twoBase.Transposable := by
  haveI : Infinite (twoBase.F.X twoBase.W₀) := inferInstanceAs (Infinite ℕ)
  haveI : DecidableEq (twoBase.F.X twoBase.W₀) := inferInstanceAs (DecidableEq ℕ)
  exact transposable_of_swaps twoBase fun y z =>
    ⟨FunCat.arr (F := twoCat) (i := false) (j := false) (Equiv.swap y z) (Equiv.swap y z).bijective,
      (Equiv.swap y z).bijective, rfl⟩

theorem two_infinitelyManyIndividuals : twoBase.model.InfinitelyManyIndividuals :=
  inferInstanceAs (Infinite ℕ)

/-- Separable collapses, the pairs `2i, 2i + 1`: every function into the second object is an
arrow, and `twoCollapse i` collapses the `i`th pair and no other. -/
theorem two_separable : twoBase.SeparableCollapses := by
  refine ⟨fun i => (2 * i : ℕ), fun i => (2 * i + 1 : ℕ), fun i j hij => ?_⟩
  refine ⟨(true : Bool), FunCat.arr (F := twoCat) (i := false) (j := true) (twoCollapse i) trivial, Or.inl ⟨?_, ?_⟩⟩
  · show twoCollapse i (2 * i) = twoCollapse i (2 * i + 1)
    simp only [twoCollapse]; split_ifs <;> omega
  · show twoCollapse i (2 * j) ≠ twoCollapse i (2 * j + 1)
    simp only [twoCollapse]; split_ifs <;> omega

end SymIdeal

/-! ### The old and new individuals -/

namespace OldNew

theorem transposable : base.Transposable := by
  haveI : Infinite (base.F.X base.W₀) := inferInstanceAs (Infinite ℕ)
  haveI : DecidableEq (base.F.X base.W₀) := inferInstanceAs (DecidableEq ℕ)
  exact SymIdeal.transposable_of_swaps base fun y z =>
    ⟨FunCat.arr (F := cat) (i := E) (j := E) (Equiv.swap y z) ⟨(Equiv.swap y z).injective, trivial⟩,
      ⟨(Equiv.swap y z).bijective, fun _ => Iff.rfl⟩, rfl⟩

theorem infinitelyManyIndividuals : base.model.InfinitelyManyIndividuals :=
  inferInstanceAs (Infinite ℕ)

end OldNew

/-! ### The finite-compression entrance -/

namespace FiniteCompression

theorem transposable : (base A).Transposable := by
  haveI : Infinite ((base A).F.X (base A).W₀) := inferInstanceAs (Infinite (ℕ × ℕ))
  haveI : DecidableEq ((base A).F.X (base A).W₀) := inferInstanceAs (DecidableEq (ℕ × ℕ))
  refine SymIdeal.transposable_of_swaps (base A) fun y z => ?_
  let g := mkRoot (Equiv.swap y z) (Equiv.swap y z).surjective
  have hgg : g ≫ g = 𝟙 A := FunCat.hom_ext (funext fun x => Equiv.swap_apply_self y z x)
  exact ⟨g, ⟨g, hgg, hgg⟩, rfl⟩

theorem infinitelyManyIndividuals : (base A).model.InfinitelyManyIndividuals :=
  inferInstanceAs (Infinite (ℕ × ℕ))

/-- Separable collapses: through `Nat.pairEquiv`, the pairs `2i + 2, 2i + 3` of `ℕ` and the
surjections `halfThen i`, which collapse the `i`th pair and no later one. -/
theorem separable : (base A).SeparableCollapses := by
  let e := Nat.pairEquiv
  have key : ∀ i : ℕ, (base A).F.Arr (i := A) (j := A) (e ∘ SymIdeal.halfThen i ∘ e.symm) :=
    fun i => e.surjective.comp ((SymIdeal.halfThen_surjective i).comp e.symm.surjective)
  refine ⟨fun i => e (2 * i + 2), fun i => e (2 * i + 3), fun i j hij => ?_⟩
  have hk : ∀ i x, FunCat.fn (FunCat.arr (F := cat) (i := A) (j := A) _ (key i)) (e x) = e (SymIdeal.halfThen i x) :=
    fun i x => by simp
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨A, FunCat.arr (F := cat) (i := A) (j := A) _ (key i), Or.inl ⟨?_, ?_⟩⟩
    · rw [hk, hk, (SymIdeal.halfThen_sep h).1]
    · rw [hk, hk]; exact fun c => (SymIdeal.halfThen_sep h).2 (e.injective c)
  · refine ⟨A, FunCat.arr (F := cat) (i := A) (j := A) _ (key j), Or.inr ⟨?_, ?_⟩⟩
    · rw [hk, hk, (SymIdeal.halfThen_sep h).1]
    · rw [hk, hk]; exact fun c => (SymIdeal.halfThen_sep h).2 (e.injective c)

end FiniteCompression

end Classicism.Meta.Intensional
