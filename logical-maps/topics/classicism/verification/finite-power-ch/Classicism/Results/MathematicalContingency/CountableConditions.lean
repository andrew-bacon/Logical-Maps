import Classicism.Results.MathematicalContingency.FiniteConditions

/-! Countable-domain partial functions, represented by rigid ternary graphs.
Domain codes are total functional injections of occupied coordinate pairs into N;
they are current relations, not chosen function terms or necessarily functional maps. -/
namespace Classicism.MathematicalContingency
variable {ν α β γ : Type} [Ty ν] [Ty α] [Ty β] [Ty γ]

def CountableDomain (N : ν → Prop) (R : α → β → γ → Prop) : Prop :=
  ∃ F : α → β → ν → Prop,
    (∀ x y n, F x y n → N n ∧ ∃ z, R x y z) ∧
    (∀ x y z, R x y z → ∃ n, F x y n) ∧
    (∀ x y n m, F x y n → F x y m → n = m) ∧
    (∀ x y u v n, F x y n → F u v n → x = u ∧ y = v)

def CountableCondition (N : ν → Prop) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) : Prop :=
  Rigid R ∧ (∀ x y z, R x y z → A x ∧ B y ∧ D z) ∧
    CountableDomain N R ∧ TernaryFunctional R

def CountableConditionOrder (N : ν → Prop) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R S : α → β → γ → Prop) : Prop :=
  CountableCondition N A B D R ∧ CountableCondition N A B D S ∧ TernaryExtends R S

theorem countableDomain_coext (N : ν → Prop) (R S : α → β → γ → Prop)
    (h : CountableDomain N R) (e : ∀ x y z, R x y z ↔ S x y z) : CountableDomain N S := by
  obtain ⟨F,hf,ht,hu,hi⟩ := h
  refine ⟨F,?_,?_,hu,hi⟩
  · intro x y n h
    obtain ⟨hn,z,hz⟩ := hf x y n h
    exact ⟨hn,z,(e x y z).mp hz⟩
  · intro x y z hz
    exact ht x y z ((e x y z).mpr hz)

theorem countableDomain_empty (N : ν → Prop) (R : α → β → γ → Prop)
    (he : TernaryEmpty R) : CountableDomain N R :=
  ⟨fun _ _ _ => True ∧ False,
    fun _ _ _ h => h.2.elim,
    fun x y z h => (he x y z h).elim,
    fun _ _ _ _ h _ => h.2.elim,
    fun _ _ _ _ _ h _ => h.2.elim⟩

theorem countableCondition_coext (N : ν → Prop) (A : α → Prop) (B : β → Prop)
    (D : γ → Prop) (R S : α → β → γ → Prop) (hr : CountableCondition N A B D R)
    (hs : Rigid S) (e : ∀ x y z, R x y z ↔ S x y z) : CountableCondition N A B D S :=
  ⟨hs,fun x y z h => hr.2.1 x y z ((e x y z).mpr h),
    countableDomain_coext N R S hr.2.2.1 e,ternaryFunctional_coext R S hr.2.2.2 e⟩

theorem countableCondition_representative (N : ν → Prop) (A : α → Prop)
    (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (α → β → γ → Prop)) (R : α → β → γ → Prop)
    (typed : ∀ x y z, R x y z → A x ∧ B y ∧ D z)
    (counted : CountableDomain N R) (functional : TernaryFunctional R) :
    ∃ S, CountableCondition N A B D S ∧ ∀ x y z, R x y z ↔ S x y z := by
  obtain ⟨S,hs,e⟩ := rc R
  exact ⟨S,⟨hs,fun x y z h => typed x y z ((e x y z).mpr h),
    countableDomain_coext N R S counted e,ternaryFunctional_coext R S functional e⟩,e⟩

theorem countableCondition_empty (N : ν → Prop) (A : α → Prop) (B : β → Prop)
    (D : γ → Prop) (rc : P.RigidComprehension (α → β → γ → Prop)) :
    ∃ R, CountableCondition N A B D R ∧ TernaryEmpty R := by
  obtain ⟨R,hr,e⟩ := countableCondition_representative N A B D rc (fun _ _ _ => True ∧ False)
    (fun _ _ _ h => h.2.elim)
    (countableDomain_empty N _ (fun _ _ _ h => h.2)) (fun _ _ _ _ h _ => h.2.elim)
  exact ⟨R,hr,fun x y z h => ((e x y z).mpr h).2⟩

theorem countableConditionOrder_partialOrder (N : ν → Prop) (A : α → Prop)
    (B : β → Prop) (D : γ → Prop) :
    PartialOrderOn (CountableCondition N A B D) (CountableConditionOrder N A B D) :=
  ⟨fun _ _ h => ⟨h.1,h.2.1⟩,
    fun R hr => ⟨hr,hr,ternaryExtends_refl R⟩,
    fun R S h k => ternaryExtends_antisymm R S h.1.1 h.2.1.1 h.2.2 k.2.2,
    fun R S T h k => ⟨h.1,k.2.1,ternaryExtends_trans R S T h.2.2 k.2.2⟩⟩

theorem countableDomain_row (N : α → Prop) (D : γ → Prop)
    (F : α → γ → Prop) (hf : Maps F N D) (a : β) :
    CountableDomain N (fun x y z => y = a ∧ F x z) := by
  refine ⟨fun x y n => y = a ∧ N x ∧ n = x,?_,?_,?_,?_⟩
  · intro x y n h
    obtain ⟨z,_,hz⟩ := hf.2.1 x h.2.1
    exact ⟨h.2.2.symm ▸ h.2.1,z,h.1,hz⟩
  · intro x y z h
    exact ⟨x,h.1,(hf.1 x z h.2).1,rfl⟩
  · intro x y n m hn hm
    exact hn.2.2.trans hm.2.2.symm
  · intro x y u v n hx hu
    exact ⟨hx.2.2.symm.trans hu.2.2,hx.1.trans hu.1.symm⟩

theorem countableCondition_row (N : α → Prop) (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (α → β → γ → Prop))
    (F : α → γ → Prop) (hf : Maps F N D) (a : β) (ha : B a) :
    ∃ R, CountableCondition N N B D R ∧ ∀ x y z, R x y z ↔ y = a ∧ F x z := by
  obtain ⟨R,hr,e⟩ := countableCondition_representative N N B D rc
    (fun x y z => y = a ∧ F x z)
    (fun x y z h => ⟨(hf.1 x z h.2).1,h.1.symm ▸ ha,(hf.1 x z h.2).2⟩)
    (countableDomain_row N D F hf a)
    (fun x y z w hz hw => hf.2.2 x z w hz.2 hw.2)
  exact ⟨R,hr,fun x y z => (e x y z).symm⟩

#classicism_check countableDomain_coext countableDomain_empty countableCondition_coext countableCondition_representative countableCondition_empty countableConditionOrder_partialOrder countableDomain_row countableCondition_row
#classicism_types countableDomain_coext countableDomain_empty countableCondition_coext countableCondition_representative countableCondition_empty countableConditionOrder_partialOrder countableDomain_row countableCondition_row
end Classicism.MathematicalContingency
