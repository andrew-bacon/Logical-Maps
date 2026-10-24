import Classicism.Models.SymBase
import Classicism.Models.PairInjCollapse

/-!
# The old/new category and its symmetric ideally-full C-model

The owning construction is models/symmetric-old-new-individuals.yaml and its
writeup. E has Nat individuals; O has Nat ⊕ Nat, with the left summand old.
All four arrow classes are represented literally. Finite pinning and target
symmetry are supplied to symIdeal_isModel, not assumed of a countermodel.

Original formalization (misc), 22 October 2026. Background: Dorr, BC does not
imply RC, Definitions 15–18 and Proposition 20, p.8. This does not copy the
withdrawn even-haecceity BC-failure argument.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory
noncomputable section

abbrev X : Bool → Type
  | false => Nat
  | true => Nat ⊕ Nat

def old : ∀ V, X V → Prop
  | false, _ => True
  | true, .inl _ => True
  | true, .inr _ => False

def ColorPres (V : Bool) (f : X V → X V) : Prop := ∀ x, old V (f x) ↔ old V x

def Shape : ∀ {W V : Bool}, (X W → X V) → Prop
  | false, false, _ => True
  | false, true, f => ∀ x, old true (f x)
  | true, false, _ => True
  | true, true, f => (Function.Bijective f ∧ ColorPres true f) ∨ ∀ x, old true (f x)

def Arr {W V : Bool} (f : X W → X V) : Prop := Function.Injective f ∧ Shape f

theorem arr_id (V : Bool) : Arr (id : X V → X V) := by
  cases V
  · exact ⟨Function.injective_id, trivial⟩
  · exact ⟨Function.injective_id, Or.inl ⟨Function.bijective_id, fun _ => Iff.rfl⟩⟩

theorem arr_comp {W V U : Bool} {f : X W → X V} {g : X V → X U}
    (hf : Arr f) (hg : Arr g) : Arr (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  cases W <;> cases V <;> cases U
  · trivial
  · exact fun x => hg.2 (f x)
  · trivial
  · rcases hg.2 with ⟨_, hp⟩ | ho
    · exact fun x => (hp (f x)).2 (hf.2 x)
    · exact fun x => ho (f x)
  · trivial
  · exact Or.inr fun x => hg.2 (f x)
  · trivial
  · rcases hf.2 with ⟨hfb, hfp⟩ | hfo
    · rcases hg.2 with ⟨hgb, hgp⟩ | hgo
      · exact Or.inl ⟨hgb.comp hfb, fun x => (hgp (f x)).trans (hfp x)⟩
      · exact Or.inr fun x => hgo (f x)
    · rcases hg.2 with ⟨_, hgp⟩ | hgo
      · exact Or.inr fun x => (hgp (f x)).2 (hfo x)
      · exact Or.inr fun x => hgo (f x)

abbrev cat : FunCat where
  Obj := Bool
  X := X
  Arr := Arr
  arr_id := arr_id
  arr_comp := arr_comp

abbrev E : cat.Ob := false
abbrev O : cat.Ob := true

def syms (V : cat.Ob) : Set (V ⟶ V) :=
  {g | Function.Bijective (FunCat.fn g) ∧ ColorPres V (FunCat.fn g)}

theorem sym_arr {V : Bool} {f : X V → X V}
    (h : Function.Bijective f ∧ ColorPres V f) : Arr f := by
  cases V
  · exact ⟨h.1.1, trivial⟩
  · exact ⟨h.1.1, Or.inl h⟩

theorem syms_inv : SymGroup syms := by
  intro V g hg
  let e := Equiv.ofBijective (FunCat.fn g) hg.1
  have hp : ColorPres V e.symm := by
    intro x
    have h := hg.2 (e.symm x)
    change old V (e (e.symm x)) ↔ old V (e.symm x) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  let gi : V ⟶ V := FunCat.arr e.symm (sym_arr ⟨e.symm.bijective, hp⟩)
  refine ⟨gi, ⟨e.symm.bijective, hp⟩, ?_, ?_⟩
  · exact FunCat.hom_ext (funext e.symm_apply_apply)
  · exact FunCat.hom_ext (funext e.apply_symm_apply)

abbrev base : SymBase where
  F := cat
  G := syms
  G_id V := ⟨Function.bijective_id, fun _ => Iff.rfl⟩
  G_comp hg hs := ⟨hs.1.comp hg.1, fun x => (hs.2 _).trans (hg.2 x)⟩
  G_inv := syms_inv
  W₀ := E
  ne V := by cases V; exact ⟨0⟩; exact ⟨Sum.inl 0⟩
  J := PinIdeal.fin _
  J_base _ h := h

abbrev model : Premodel Signature.pure cat.Ob := base.model

theorem isModel : model.IsModel := base.model_isModel

def canonFn : ∀ V : cat.Ob, Nat → X V
  | false => id
  | true => Sum.inl

theorem canon_injective (V : cat.Ob) : Function.Injective (canonFn V) := by
  cases V
  · exact Function.injective_id
  · exact Sum.inl_injective

def canon (V : cat.Ob) : E ⟶ V :=
  FunCat.arr (canonFn V) (by
    cases V
    · exact ⟨Function.injective_id, trivial⟩
    · exact ⟨Sum.inl_injective, fun _ => trivial⟩)

@[simp] theorem canon_E : canon E = 𝟙 E := rfl

def oldIndex : Nat ⊕ Nat → Nat := Sum.elim id (fun _ => 0)

theorem inl_oldIndex (x : Nat ⊕ Nat) (h : old true x) : Sum.inl (oldIndex x) = x := by
  cases x with
  | inl n => rfl
  | inr n => exact h.elim

def coord {V : cat.Ob} (h : E ⟶ V) : Nat → Nat :=
  match V with
  | false => FunCat.fn h
  | true => oldIndex ∘ FunCat.fn h

theorem canon_coord {V : cat.Ob} (h : E ⟶ V) (n : Nat) :
    canonFn V (coord h n) = FunCat.fn h n := by
  cases V
  · rfl
  · exact inl_oldIndex _ (h.2.2 n)

theorem coord_injective {V : cat.Ob} (h : E ⟶ V) : Function.Injective (coord h) := by
  intro a b hab
  apply h.2.1
  change FunCat.fn h a = FunCat.fn h b
  rw [← canon_coord h a, ← canon_coord h b, hab]

def permE (e : Nat ≃ Nat) : E ⟶ E :=
  FunCat.arr e ⟨e.injective, trivial⟩

theorem permE_sym (e : Nat ≃ Nat) : permE e ∈ syms E :=
  ⟨e.bijective, fun _ => Iff.rfl⟩

def liftPerm (V : cat.Ob) (e : Nat ≃ Nat) : X V ≃ X V :=
  match V with
  | false => e
  | true => Equiv.sumCongr e (Equiv.refl Nat)

theorem liftPerm_color (V : cat.Ob) (e : Nat ≃ Nat) : ColorPres V (liftPerm V e) := by
  cases V
  · exact fun _ => Iff.rfl
  · intro x; cases x <;> rfl

def lifted (V : cat.Ob) (e : Nat ≃ Nat) : V ⟶ V :=
  FunCat.arr (liftPerm V e) (sym_arr ⟨(liftPerm V e).bijective, liftPerm_color V e⟩)

theorem lifted_sym (V : cat.Ob) (e : Nat ≃ Nat) : lifted V e ∈ syms V :=
  ⟨(liftPerm V e).bijective, liftPerm_color V e⟩

theorem canon_lifted (V : cat.Ob) (e : Nat ≃ Nat) :
    canon V ≫ lifted V e = permE e ≫ canon V := by
  apply FunCat.hom_ext
  funext n
  cases V <;> rfl

/-- Every root arrow agrees on a finite pin with a target symmetry after the
canonical arrow. No surjectivity of arbitrary higher-type transport is used. -/
theorem approximate {V : cat.Ob} (h : E ⟶ V) {S : Set Nat} (hS : S.Finite) :
    ∃ g ∈ syms V, AgreeOn cat.De (W := E) S h (canon V ≫ g) := by
  obtain ⟨e, he⟩ := Monoids.PairInjCol.exists_perm_extend hS (coord h) (coord_injective h).injOn
  refine ⟨lifted V e, lifted_sym V e, fun n hn => ?_⟩
  change FunCat.fn h n = (liftPerm V e) (canonFn V n)
  have hh := canon_coord h n
  rw [← he n hn] at hh
  cases V <;> exact hh.symm

/-- A target symmetry factors through the canonical arrow by a root symmetry.
Its unrestricted new-coordinate permutation causes no obstruction. -/
theorem factor_sym {V : cat.Ob} (g : V ⟶ V) (hg : g ∈ syms V) :
    ∃ s ∈ syms E, canon V ≫ g = s ≫ canon V := by
  cases V
  · exact ⟨g, hg, FunCat.hom_ext rfl⟩
  · let f : Nat → Nat := fun n => oldIndex (FunCat.fn g (Sum.inl n))
    have hf : ∀ n, Sum.inl (f n) = FunCat.fn g (Sum.inl n) :=
      fun n => inl_oldIndex _ ((hg.2 (Sum.inl n)).2 trivial)
    have hfi : Function.Injective f := by
      intro a b h
      apply Sum.inl_injective
      apply hg.1.1
      rw [← hf a, ← hf b, h]
    have hfs : Function.Surjective f := by
      intro n
      obtain ⟨x, hx⟩ := hg.1.2 (Sum.inl n)
      have ho : old true x := (hg.2 x).1 (by rw [hx]; trivial)
      refine ⟨oldIndex x, ?_⟩
      apply Sum.inl_injective
      rw [hf, inl_oldIndex x ho, hx]
    let e := Equiv.ofBijective f ⟨hfi, hfs⟩
    refine ⟨permE e, permE_sym e, FunCat.hom_ext (funext fun n => (hf n).symm)⟩

def code : ∀ V : cat.Ob, X V ≃ Nat
  | false => Equiv.refl Nat
  | true => Equiv.natSumNatEquivNat

/-- A finite partial injection between either countable domain extends to a
bijection of the underlying sets. Admissibility is imposed separately. -/
theorem extend_finite {W V : cat.Ob} {D : Set (X W)} (hD : D.Finite)
    (f : X W → X V) (hf : Set.InjOn f D) :
    ∃ e : X W ≃ X V, ∀ x ∈ D, e x = f x := by
  let fn : Nat → Nat := fun n => code V (f ((code W).symm n))
  have hi : Set.InjOn fn (code W '' D) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have he : f a = f b := (code V).injective (by simpa [fn] using hab)
    exact congrArg (code W) (hf ha hb he)
  obtain ⟨s, hs⟩ := Monoids.PairInjCol.exists_perm_extend (hD.image (code W)) fn hi
  refine ⟨((code W).trans s).trans (code V).symm, fun x hx => ?_⟩
  apply (code V).injective
  simpa [fn] using hs (code W x) ⟨x, hx, rfl⟩

theorem into_old_arr {W V : cat.Ob} (f : X W → Nat) (hf : Function.Injective f) :
    Arr (canonFn V ∘ f) := by
  refine ⟨(canon_injective V).comp hf, ?_⟩
  cases W <;> cases V
  · trivial
  · exact fun _ => trivial
  · trivial
  · exact Or.inr fun _ => trivial

/-- The finite invertibility needed for root ND, with all four source/target
cases handled by an explicit extension into the old part of the target. -/
theorem finite_inverse {V U : cat.Ob} (f : E ⟶ V) (h : E ⟶ U)
    {S : Set Nat} (hS : S.Finite) :
    ∃ k : V ⟶ U, AgreeOn cat.De (W := E) S (f ≫ k) h := by
  classical
  let q : X V → Nat := coord h ∘ Function.invFun (FunCat.fn f)
  have hq : Set.InjOn q (FunCat.fn f '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have he : coord h a = coord h b := by
      change coord h (Function.invFun (FunCat.fn f) (FunCat.fn f a)) =
        coord h (Function.invFun (FunCat.fn f) (FunCat.fn f b)) at hab
      rw [(Function.leftInverse_invFun f.2.1) a,
        (Function.leftInverse_invFun f.2.1) b] at hab
      exact hab
    exact congrArg (FunCat.fn f) (coord_injective h he)
  obtain ⟨e, he⟩ := extend_finite (V := E) (hS.image (FunCat.fn f)) q hq
  let k : V ⟶ U := FunCat.arr (canonFn U ∘ e) (into_old_arr e e.injective)
  refine ⟨k, fun n hn => ?_⟩
  change canonFn U (e (FunCat.fn f n)) = FunCat.fn h n
  rw [he _ ⟨n, hn, rfl⟩]
  change canonFn U (coord h (Function.invFun (FunCat.fn f) (FunCat.fn f n))) = _
  rw [(Function.leftInverse_invFun f.2.1) n]
  exact canon_coord h n

def back : O ⟶ E := FunCat.arr (code O) ⟨(code O).injective, trivial⟩

end
end Classicism.Meta.Intensional.OldNew
