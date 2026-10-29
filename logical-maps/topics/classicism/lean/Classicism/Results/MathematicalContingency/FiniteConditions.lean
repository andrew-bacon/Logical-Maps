import Classicism.Results.MathematicalContingency.FiniteTernary

/-! Rigid finite ternary partial-function graphs, with current functionality.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
The forcing order is reverse graph inclusion. No necessary functionality or
necessity of distinctness for the coordinate carrier is assumed. -/
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

def TernaryFunctional (R : α → β → γ → Prop) : Prop :=
  ∀ x y b c, R x y b → R x y c → b = c

def TernaryAgree (R S : α → β → γ → Prop) : Prop :=
  ∀ x y b c, R x y b → S x y c → b = c

def TernaryExtends (R S : α → β → γ → Prop) : Prop := ∀ x y z, S x y z → R x y z

def FiniteCondition (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) : Prop :=
  Rigid R ∧ FiniteTernary A B D R ∧ TernaryFunctional R

def ConditionOrder (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R S : α → β → γ → Prop) : Prop :=
  FiniteCondition A B D R ∧ FiniteCondition A B D S ∧ TernaryExtends R S

theorem ternaryExtends_refl (R : α → β → γ → Prop) : TernaryExtends R R := fun _ _ _ h => h

theorem ternaryExtends_trans (R S T : α → β → γ → Prop)
    (h : TernaryExtends R S) (k : TernaryExtends S T) : TernaryExtends R T :=
  fun x y z ht => h x y z (k x y z ht)

theorem ternaryExtends_antisymm (R S : α → β → γ → Prop) (hr : Rigid R) (hs : Rigid S)
    (h : TernaryExtends R S) (k : TernaryExtends S R) : R = S :=
  rigid_eq_of_coext R S hr hs (fun x y z => ⟨k x y z,h x y z⟩)

theorem ternaryFunctional_coext (R S : α → β → γ → Prop) (h : TernaryFunctional R)
    (e : ∀ x y z, R x y z ↔ S x y z) : TernaryFunctional S :=
  fun x y b c hb hc => h x y b c ((e x y b).mpr hb) ((e x y c).mpr hc)

theorem ternaryFunctional_subset (R S : α → β → γ → Prop) (h : TernaryFunctional R)
    (k : TernaryExtends R S) : TernaryFunctional S :=
  fun x y b c hb hc => h x y b c (k x y b hb) (k x y c hc)

theorem ternaryAgree_symm (R S : α → β → γ → Prop) (h : TernaryAgree R S) : TernaryAgree S R :=
  fun x y b c hb hc => (h x y c b hc hb).symm

theorem ternaryFunctional_union (R S : α → β → γ → Prop)
    (hr : TernaryFunctional R) (hs : TernaryFunctional S) (h : TernaryAgree R S) :
    TernaryFunctional (fun x y z => R x y z ∨ S x y z) := by
  intro x y b c hb hc
  exact hb.elim (fun hb => hc.elim (hr x y b c hb) (h x y b c hb))
    (fun hb => hc.elim (fun hc => (h x y c b hc hb).symm) (hs x y b c hb))

variable (A : α → Prop) (B : β → Prop) (D : γ → Prop)

theorem finiteCondition_coext (R S : α → β → γ → Prop) (hr : FiniteCondition A B D R)
    (hs : Rigid S) (e : ∀ x y z, R x y z ↔ S x y z) : FiniteCondition A B D S :=
  ⟨hs,finiteTernary_coext A B D R S hr.2.1 e,ternaryFunctional_coext R S hr.2.2 e⟩

theorem finiteCondition_representative (rc : P.RigidComprehension (α → β → γ → Prop))
    (R : α → β → γ → Prop) (hf : FiniteTernary A B D R) (hu : TernaryFunctional R) :
    ∃ S, FiniteCondition A B D S ∧ ∀ x y z, R x y z ↔ S x y z := by
  obtain ⟨S,hs,e⟩ := rc R
  exact ⟨S,⟨hs,finiteTernary_coext A B D R S hf e,ternaryFunctional_coext R S hu e⟩,e⟩

theorem finiteCondition_empty (rc : P.RigidComprehension (α → β → γ → Prop)) :
    ∃ R, FiniteCondition A B D R ∧ TernaryEmpty R := by
  obtain ⟨R,hr,e⟩ := finiteCondition_representative A B D rc (fun _ _ _ => True ∧ False)
    (finiteTernary_empty A B D _ (fun _ _ _ h => h.2)) (fun _ _ _ _ h _ => h.2.elim)
  exact ⟨R,hr,fun x y z h => ((e x y z).mpr h).2⟩

theorem conditionOrder_partialOrder : PartialOrderOn (FiniteCondition A B D) (ConditionOrder A B D) :=
  ⟨fun _ _ h => ⟨h.1,h.2.1⟩,
    fun R hr => ⟨hr,hr,ternaryExtends_refl R⟩,
    fun R S h k => ternaryExtends_antisymm R S h.1.1 h.2.1.1 h.2.2 k.2.2,
    fun R S T h k => ⟨h.1,k.2.1,ternaryExtends_trans R S T h.2.2 k.2.2⟩⟩

theorem finiteCondition_compatible_iff (rc : P.RigidComprehension (α → β → γ → Prop))
    (R S : α → β → γ → Prop) (hr : FiniteCondition A B D R) (hs : FiniteCondition A B D S) :
    (∃ T, FiniteCondition A B D T ∧ TernaryExtends T R ∧ TernaryExtends T S) ↔ TernaryAgree R S := by
  constructor
  · intro ⟨T,ht,he,hf⟩ x y b c hb hc
    exact ht.2.2 x y b c (he x y b hb) (hf x y c hc)
  · intro h
    obtain ⟨T,ht,e⟩ := finiteCondition_representative A B D rc (fun x y z => R x y z ∨ S x y z)
      (finiteTernary_union A B D R S hr.2.1 hs.2.1) (ternaryFunctional_union R S hr.2.2 hs.2.2 h)
    exact ⟨T,ht,fun x y z h => (e x y z).mp (Or.inl h),fun x y z h => (e x y z).mp (Or.inr h)⟩

/-- The representative of a compatible union is the greatest common strengthening. -/
theorem finiteCondition_union_infimum (rc : P.RigidComprehension (α → β → γ → Prop))
    (R S : α → β → γ → Prop) (hr : FiniteCondition A B D R) (hs : FiniteCondition A B D S)
    (h : TernaryAgree R S) :
    ∃ T, FiniteCondition A B D T ∧ TernaryExtends T R ∧ TernaryExtends T S ∧
      ∀ U, TernaryExtends U R → TernaryExtends U S → TernaryExtends U T := by
  obtain ⟨T,ht,e⟩ := finiteCondition_representative A B D rc (fun x y z => R x y z ∨ S x y z)
    (finiteTernary_union A B D R S hr.2.1 hs.2.1) (ternaryFunctional_union R S hr.2.2 hs.2.2 h)
  refine ⟨T,ht,fun x y z h => (e x y z).mp (Or.inl h),fun x y z h => (e x y z).mp (Or.inr h),?_⟩
  intro U hu hv x y z ht
  exact ((e x y z).mpr ht).elim (hu x y z) (hv x y z)

theorem finiteCondition_add_fresh (rc : P.RigidComprehension (α → β → γ → Prop))
    (R : α → β → γ → Prop) (hr : FiniteCondition A B D R) (x : α) (y : β) (z : γ)
    (hx : A x) (hy : B y) (hz : D z) (fresh : ∀ b, ¬ R x y b) :
    ∃ S, FiniteCondition A B D S ∧ TernaryInsert x y z R S := by
  let T : α → β → γ → Prop := fun u v w => R u v w ∨ (u = x ∧ v = y ∧ w = z)
  have hf : FiniteTernary A B D T := finiteTernary_insert A B D R T x y z hx hy hz
    (fun _ _ _ => Iff.rfl) hr.2.1
  have hu : TernaryFunctional T := by
    intro u v w t hw ht
    obtain hw | ⟨eu,ev,ew⟩ := hw
    · obtain ht | ⟨eu,ev,et⟩ := ht
      · exact hr.2.2 u v w t hw ht
      · subst u; subst v
        exact (fresh w hw).elim
    · subst u; subst v; subst w
      obtain ht | ⟨_,_,et⟩ := ht
      · exact (fresh t ht).elim
      · exact et.symm
  obtain ⟨S,hs,e⟩ := finiteCondition_representative A B D rc T hf hu
  exact ⟨S,hs,fun u v w => (e u v w).symm⟩

theorem finiteCondition_decides_coordinate (rc : P.RigidComprehension (α → β → γ → Prop))
    (R : α → β → γ → Prop) (hr : FiniteCondition A B D R) (x : α) (y : β)
    (hx : A x) (hy : B y) (d : γ) (hd : D d) :
    ∃ S, FiniteCondition A B D S ∧ TernaryExtends S R ∧ ∃ b, S x y b := by
  obtain he | he := em (∃ b, R x y b)
  · exact ⟨R,hr,ternaryExtends_refl R,he⟩
  · obtain ⟨S,hs,hi⟩ := finiteCondition_add_fresh A B D rc R hr x y d hx hy hd (fun b hb => he ⟨b,hb⟩)
    exact ⟨S,hs,fun u v w h => (hi u v w).mpr (Or.inl h),d,(hi x y d).mpr (Or.inr ⟨rfl,rfl,rfl⟩)⟩

#classicism_check ternaryExtends_refl ternaryExtends_trans ternaryExtends_antisymm
  ternaryFunctional_coext ternaryFunctional_subset ternaryAgree_symm ternaryFunctional_union
  finiteCondition_coext finiteCondition_representative finiteCondition_empty
  conditionOrder_partialOrder finiteCondition_compatible_iff finiteCondition_union_infimum
  finiteCondition_add_fresh finiteCondition_decides_coordinate
#classicism_types ternaryExtends_refl ternaryExtends_trans ternaryExtends_antisymm
  ternaryFunctional_coext ternaryFunctional_subset ternaryAgree_symm ternaryFunctional_union
  finiteCondition_coext finiteCondition_representative finiteCondition_empty
  conditionOrder_partialOrder finiteCondition_compatible_iff finiteCondition_union_infimum
  finiteCondition_add_fresh finiteCondition_decides_coordinate
end Classicism.MathematicalContingency
