import Classicism.Results.MathematicalContingency.FiniteSubsets

/-! Finite-subset absorption from pairing on a well-ordered carrier.
Codes live in that carrier, not in the natural numbers. No choice function is used.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

def FiniteSetCode (K : α → Prop) (z : α) (C : α → α → α → Prop)
    (X : α → Prop) (c : α) : Prop :=
  ∀ P : (α → Prop) → α → Prop,
    (∀ X, K z → (∀ x, ¬ X x) → P X z) →
    (∀ X Y x c d, K x → K c → K d → (∀ u, Y u ↔ X u ∨ u = x) →
      C x c d → P X c → P Y d) → P X c

variable (K : α → Prop) (z : α) (C : α → α → α → Prop)

theorem finiteSetCode_empty (X : α → Prop) (hz : K z) (he : ∀ x, ¬ X x) :
    FiniteSetCode K z C X z := fun _ h0 _ => h0 X hz he

theorem finiteSetCode_insert (X Y : α → Prop) (x c d : α) (hx : K x) (hc : K c) (hd : K d)
    (hi : ∀ u, Y u ↔ X u ∨ u = x) (hC : C x c d) (h : FiniteSetCode K z C X c) :
    FiniteSetCode K z C Y d := fun P h0 hs => hs X Y x c d hx hc hd hi hC (h P h0 hs)

theorem finiteSetCode_induction (P : (α → Prop) → α → Prop)
    (h0 : ∀ X, K z → (∀ x, ¬ X x) → P X z)
    (hs : ∀ X Y x c d, K x → K c → K d → (∀ u, Y u ↔ X u ∨ u = x) →
      C x c d → FiniteSetCode K z C X c → P X c → P Y d)
    (X : α → Prop) (c : α) (h : FiniteSetCode K z C X c) : P X c :=
  (h (fun X c => FiniteSetCode K z C X c ∧ P X c)
    (fun X hz he => ⟨finiteSetCode_empty K z C X hz he,h0 X hz he⟩)
    (fun X Y x c d hx hc hd hi hC ih =>
      ⟨finiteSetCode_insert K z C X Y x c d hx hc hd hi hC ih.1,
       hs X Y x c d hx hc hd hi hC ih.1 ih.2⟩)).2

theorem finiteSetCode_data (X : α → Prop) (c : α) (h : FiniteSetCode K z C X c) :
    FiniteSubset K X ∧ K c :=
  h (fun X c => FiniteSubset K X ∧ K c)
    (fun X hz he => ⟨finiteSubset_empty K X he,hz⟩)
    (fun X Y x _ d hx _ hd hi _ ih => ⟨finiteSubset_insert K X Y x hx hi ih.1,hd⟩)

theorem finiteSetCode_cases (X : α → Prop) (c : α) (h : FiniteSetCode K z C X c) :
    ((∀ x, ¬ X x) ∧ c = z ∧ K z) ∨
    ∃ Y x b, K x ∧ K b ∧ K c ∧ (∀ u, X u ↔ Y u ∨ u = x) ∧ C x b c ∧ FiniteSetCode K z C Y b :=
  finiteSetCode_induction K z C
    (fun X c => ((∀ x, ¬ X x) ∧ c = z ∧ K z) ∨
      ∃ Y x b, K x ∧ K b ∧ K c ∧ (∀ u, X u ↔ Y u ∨ u = x) ∧ C x b c ∧ FiniteSetCode K z C Y b)
    (fun X hz he => Or.inl ⟨he,rfl,hz⟩)
    (fun X Y x b c hx hb hc hi hC h _ => Or.inr ⟨X,x,b,hx,hb,hc,hi,hC,h⟩) X c h

theorem finiteSetCode_total (hz : K z)
    (total : ∀ x c, K x → K c → ∃ d, K d ∧ C x c d)
    (X : α → Prop) (hf : FiniteSubset K X) : ∃ c, K c ∧ FiniteSetCode K z C X c :=
  hf (fun X => ∃ c, K c ∧ FiniteSetCode K z C X c)
    (fun X he => ⟨z,hz,finiteSetCode_empty K z C X hz he⟩)
    (fun X Y x hx hi ih => ih.elim fun c hc => (total x c hx hc.1).elim fun d hd =>
      ⟨d,hd.1,finiteSetCode_insert K z C X Y x c d hx hc.1 hd.1 hi hd.2 hc.2⟩)

theorem finiteSetCode_decode
    (disjoint : ∀ x c, ¬ C x c z)
    (injective : ∀ x y c d v, C x c v → C y d v → x = y ∧ c = d)
    (X Y : α → Prop) (c : α) (hx : FiniteSetCode K z C X c) (hy : FiniteSetCode K z C Y c) :
    ∀ u, X u ↔ Y u := by
  have main : ∀ X c, FiniteSetCode K z C X c → ∀ Y, FiniteSetCode K z C Y c → ∀ u, X u ↔ Y u := by
    intro X c h
    apply finiteSetCode_induction K z C (fun X c => ∀ Y, FiniteSetCode K z C Y c → ∀ u, X u ↔ Y u) ?_ ?_ X c h
    · intro X _ he Y hy
      obtain ⟨hf,_,_⟩ | ⟨Z,y,b,_,_,_,_,hC,_⟩ := finiteSetCode_cases K z C Y z hy
      · exact fun u => ⟨fun h => (he u h).elim,fun h => (hf u h).elim⟩
      · exact (disjoint y b hC).elim
    · intro X Y x b c _ _ _ hi hC _ ih Z hz
      obtain ⟨_,e,_⟩ | ⟨W,y,d,_,_,_,hj,hD,hW⟩ := finiteSetCode_cases K z C Z c hz
      · exact (disjoint x b (e ▸ hC)).elim
      · obtain ⟨ex,eb⟩ := injective x y b d c hC hD
        subst y; subst d
        have e := ih W hW
        intro u
        exact (hi u).trans ((Iff.intro
          (fun h => h.elim (fun h => Or.inl ((e u).mp h)) Or.inr)
          (fun h => h.elim (fun h => Or.inl ((e u).mpr h)) Or.inr)).trans (hj u).symm)
  exact main X c hx Y hy

theorem finitePower_absorption_of_constructors (L : α → α → Prop) (hw : WellOrderOn K L)
    (hz : K z) (total : ∀ x c, K x → K c → ∃ d, K d ∧ C x c d)
    (disjoint : ∀ x c, ¬ C x c z)
    (injective : ∀ x y c d v, C x c v → C y d v → x = y ∧ c = d) :
    Embeds (RigidFinitePower K) K := by
  refine ⟨fun X c => RigidFinitePower K X ∧ FiniteSetCode K z C X c ∧
    ∀ d, FiniteSetCode K z C X d → ¬ L d c,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro X c h; exact ⟨h.1,(finiteSetCode_data K z C X c h.2.1).2⟩
  · intro X hx
    obtain ⟨b,_,hb⟩ := finiteSetCode_total K z C hz total X hx.2
    obtain ⟨c,hc,hm⟩ := hw.2 (FiniteSetCode K z C X)
      (fun d hd => (finiteSetCode_data K z C X d hd).2) ⟨b,hb⟩
    exact ⟨c,(finiteSetCode_data K z C X c hc).2,hx,hc,hm⟩
  · intro X c d hc hd
    obtain e | h | h := hw.1.2.2.2 c d
      (finiteSetCode_data K z C X c hc.2.1).2 (finiteSetCode_data K z C X d hd.2.1).2
    · exact e
    · exact (hd.2.2 c hc.2.1 h).elim
    · exact (hc.2.2 d hd.2.1 h).elim
  · intro X Y c hx hy
    exact rigid_eq_of_coext X Y hx.1.1 hy.1.1 (finiteSetCode_decode K z C disjoint injective X Y c hx.2.1 hy.2.1)

#classicism_check finiteSetCode_empty finiteSetCode_insert finiteSetCode_induction finiteSetCode_data finiteSetCode_cases finiteSetCode_total finiteSetCode_decode finitePower_absorption_of_constructors
#classicism_types finiteSetCode_empty finiteSetCode_insert finiteSetCode_induction finiteSetCode_data finiteSetCode_cases finiteSetCode_total finiteSetCode_decode finitePower_absorption_of_constructors
end Classicism.MathematicalContingency
