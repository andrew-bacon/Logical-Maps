import Classicism.Results.MathematicalContingency.FiniteSubsets

/-! Direct finite-graph cardinal comparisons via relational images.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
Tuple injections and absorption of finite subsets are explicit hypotheses. -/
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

def TernaryImage (E : α → β → γ → δ → Prop) (R : α → β → γ → Prop) : δ → Prop :=
  fun d => ∃ x y z, R x y z ∧ E x y z d

def RigidFiniteTernary (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) : Prop := Rigid R ∧ FiniteTernary A B D R

variable (A : α → Prop) (B : β → Prop) (D : γ → Prop) (K : δ → Prop)
  (E : α → β → γ → δ → Prop)

theorem ternaryImage_empty (R : α → β → γ → Prop) (he : TernaryEmpty R) :
    ∀ d, ¬ TernaryImage E R d := by
  intro d h
  obtain ⟨x,y,z,hr,_⟩ := h
  exact he x y z hr

theorem ternaryImage_insert (R S : α → β → γ → Prop) (x : α) (y : β) (z : γ)
    (hi : TernaryInsert x y z R S) (d : δ) (hd : E x y z d)
    (functional : ∀ x y z d e, E x y z d → E x y z e → d = e) :
    ∀ e, TernaryImage E S e ↔ TernaryImage E R e ∨ e = d := by
  intro e
  constructor
  · intro ⟨u,v,w,hs,he⟩
    obtain hr | ⟨hu,hv,hw⟩ := (hi u v w).mp hs
    · exact Or.inl ⟨u,v,w,hr,he⟩
    · subst u; subst v; subst w
      exact Or.inr (functional x y z e d he hd)
  · intro h
    obtain h | h := h
    · obtain ⟨u,v,w,hr,he⟩ := h
      exact ⟨u,v,w,(hi u v w).mpr (Or.inl hr),he⟩
    · subst e
      exact ⟨x,y,z,(hi x y z).mpr (Or.inr ⟨rfl,rfl,rfl⟩),hd⟩

theorem finiteTernary_image
    (total : ∀ x y z, A x → B y → D z → ∃ d, K d ∧ E x y z d)
    (functional : ∀ x y z d e, E x y z d → E x y z e → d = e)
    (R : α → β → γ → Prop) (hf : FiniteTernary A B D R) :
    FiniteSubset K (TernaryImage E R) := by
  exact hf (fun R => FiniteSubset K (TernaryImage E R))
    (fun R he => finiteSubset_empty K _ (ternaryImage_empty E R he)) (by
      intro R S x y z hx hy hz hi ih
      obtain ⟨d,hd,he⟩ := total x y z hx hy hz
      exact finiteSubset_insert K _ _ d hd (ternaryImage_insert E R S x y z hi d he functional) ih)

theorem ternaryImage_reflect
    (total : ∀ x y z, A x → B y → D z → ∃ d, K d ∧ E x y z d)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w)
    (R S : α → β → γ → Prop) (hr : FiniteTernary A B D R)
    (hsub : ∀ d, TernaryImage E R d → TernaryImage E S d) : TernaryExtends S R := by
  intro x y z h
  obtain ⟨hx,hy,hz⟩ := finiteTernary_members A B D R hr x y z h
  obtain ⟨d,_,he⟩ := total x y z hx hy hz
  obtain ⟨u,v,w,hs,hf⟩ := hsub d ⟨x,y,z,h,he⟩
  obtain ⟨hu,hv,hw⟩ := injective x y z u v w d he hf
  subst u; subst v; subst w
  exact hs

theorem ternaryImage_rigid_injective
    (total : ∀ x y z, A x → B y → D z → ∃ d, K d ∧ E x y z d)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w)
    (R S : α → β → γ → Prop) (hr : RigidFiniteTernary A B D R)
    (hs : RigidFiniteTernary A B D S) (e : ∀ d, TernaryImage E R d ↔ TernaryImage E S d) : R = S :=
  ternaryExtends_antisymm R S hr.1 hs.1
    (ternaryImage_reflect A B D K E total injective S R hs.2 (fun d => (e d).mpr))
    (ternaryImage_reflect A B D K E total injective R S hr.2 (fun d => (e d).mp))

theorem rigidFiniteTernary_embeds_finitePower (rc : P.RigidComprehension (δ → Prop))
    (total : ∀ x y z, A x → B y → D z → ∃ d, K d ∧ E x y z d)
    (functional : ∀ x y z d e, E x y z d → E x y z e → d = e)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w) :
    Embeds (RigidFiniteTernary A B D) (RigidFinitePower K) := by
  refine ⟨fun R X => RigidFiniteTernary A B D R ∧ RigidFinitePower K X ∧
    ∀ d, TernaryImage E R d ↔ X d,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro R X h; exact ⟨h.1,h.2.1⟩
  · intro R hr
    obtain ⟨X,hX,e⟩ := finiteSubset_rigid_representative rc K _
      (finiteTernary_image A B D K E total functional R hr.2)
    exact ⟨X,hX,hr,hX,e⟩
  · intro R X Y hx hy
    exact rigid_eq_of_coext X Y hx.2.1.1 hy.2.1.1 (fun d => (hx.2.2 d).symm.trans (hy.2.2 d))
  · intro R S X hr hs
    exact ternaryImage_rigid_injective A B D K E total injective R S hr.1 hs.1
      (fun d => (hr.2.2 d).trans (hs.2.2 d).symm)

theorem finiteCondition_embeds_finitePower (rc : P.RigidComprehension (δ → Prop))
    (total : ∀ x y z, A x → B y → D z → ∃ d, K d ∧ E x y z d)
    (functional : ∀ x y z d e, E x y z d → E x y z e → d = e)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w) :
    Embeds (FiniteCondition A B D) (RigidFinitePower K) :=
  embeds_trans _ (RigidFiniteTernary A B D) _
    (embeds_of_subset _ _ (fun _ h => ⟨h.1,h.2.1⟩))
    (rigidFiniteTernary_embeds_finitePower A B D K E rc total functional injective)

theorem finiteCondition_cardinal_bound (rc : P.RigidComprehension (δ → Prop))
    (total : ∀ x y z, A x → B y → D z → ∃ d, K d ∧ E x y z d)
    (functional : ∀ x y z d e, E x y z d → E x y z e → d = e)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w)
    (absorb : Embeds (RigidFinitePower K) K) : Embeds (FiniteCondition A B D) K :=
  embeds_trans _ _ _ (finiteCondition_embeds_finitePower A B D K E rc total functional injective) absorb

#classicism_check ternaryImage_empty ternaryImage_insert finiteTernary_image ternaryImage_reflect ternaryImage_rigid_injective rigidFiniteTernary_embeds_finitePower finiteCondition_embeds_finitePower finiteCondition_cardinal_bound
#classicism_types ternaryImage_empty ternaryImage_insert finiteTernary_image ternaryImage_reflect ternaryImage_rigid_injective rigidFiniteTernary_embeds_finitePower finiteCondition_embeds_finitePower finiteCondition_cardinal_bound
end Classicism.MathematicalContingency
