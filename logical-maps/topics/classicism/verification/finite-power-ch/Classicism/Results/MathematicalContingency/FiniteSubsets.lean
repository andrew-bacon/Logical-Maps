import Classicism.Results.MathematicalContingency.CarrierTheory
import Classicism.Results.MathematicalContingency.FiniteConditions

/-! Current finite subsets and rigid representatives.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def FiniteSubset (A X : α → Prop) : Prop :=
  ∀ P : (α → Prop) → Prop,
    (∀ X, (∀ x, ¬ X x) → P X) →
    (∀ X Y a, A a → (∀ x, Y x ↔ X x ∨ x = a) → P X → P Y) → P X

def RigidFinitePower (A X : α → Prop) : Prop := Rigid X ∧ FiniteSubset A X

theorem finiteSubset_empty (A X : α → Prop) (he : ∀ x, ¬ X x) : FiniteSubset A X :=
  fun _ h0 _ => h0 X he

theorem finiteSubset_insert (A X Y : α → Prop) (a : α) (ha : A a)
    (hi : ∀ x, Y x ↔ X x ∨ x = a) (hf : FiniteSubset A X) : FiniteSubset A Y :=
  fun P h0 hs => hs X Y a ha hi (hf P h0 hs)

theorem finiteSubset_induction (A : α → Prop) (P : (α → Prop) → Prop)
    (h0 : ∀ X, (∀ x, ¬ X x) → P X)
    (hs : ∀ X Y a, A a → (∀ x, Y x ↔ X x ∨ x = a) → FiniteSubset A X → P X → P Y)
    (X : α → Prop) (hf : FiniteSubset A X) : P X :=
  (hf (fun X => FiniteSubset A X ∧ P X)
    (fun X he => ⟨finiteSubset_empty A X he,h0 X he⟩)
    (fun X Y a ha hi ih => ⟨finiteSubset_insert A X Y a ha hi ih.1,hs X Y a ha hi ih.1 ih.2⟩)).2

theorem finiteSubset_members (A X : α → Prop) (hf : FiniteSubset A X) : ∀ x, X x → A x :=
  hf (fun X => ∀ x, X x → A x) (fun _ he x hx => (he x hx).elim)
    (fun X Y a ha hi ih x hx => ((hi x).mp hx).elim (ih x) (fun e => e ▸ ha))

theorem finiteSubset_coext (A X Y : α → Prop) (hf : FiniteSubset A X)
    (e : ∀ x, X x ↔ Y x) : FiniteSubset A Y := by
  have h := hf (fun X => ∀ Y, (∀ x, X x ↔ Y x) → FiniteSubset A Y)
    (fun X he Y e => finiteSubset_empty A Y (fun x hy => he x ((e x).mpr hy)))
    (fun X Z a ha hi ih Y e => finiteSubset_insert A X Y a ha
      (fun x => (e x).symm.trans (hi x)) (ih X (fun _ => Iff.rfl)))
  exact h Y e

theorem finiteSubset_singleton (A : α → Prop) (a : α) (ha : A a) :
    FiniteSubset A (fun x => x = a) :=
  finiteSubset_insert A (fun _ => False) _ a ha
    (fun _ => ⟨Or.inr,fun h => h.elim False.elim id⟩)
    (finiteSubset_empty A _ (fun _ h => h))

theorem finiteSubset_union (A X Y : α → Prop) (hx : FiniteSubset A X) (hy : FiniteSubset A Y) :
    FiniteSubset A (fun x => X x ∨ Y x) := by
  exact hx (fun X => FiniteSubset A (fun x => X x ∨ Y x))
    (fun X he => finiteSubset_coext A Y _ hy (fun x => ⟨Or.inr,
      fun h => h.elim (fun hx => (he x hx).elim) id⟩))
    (fun X Z a ha hi ih => finiteSubset_insert A (fun x => X x ∨ Y x) _ a ha
      (fun x => ⟨fun h => h.elim (fun hz => ((hi x).mp hz).elim
        (fun hx => Or.inl (Or.inl hx)) Or.inr) (fun hy => Or.inl (Or.inr hy)),
        fun h => h.elim (fun h => h.elim (fun hx => Or.inl ((hi x).mpr (Or.inl hx))) Or.inr)
          (fun e => Or.inl ((hi x).mpr (Or.inr e)))⟩) ih)

theorem finiteSubset_subset (A X Y : α → Prop) (hx : FiniteSubset A X)
    (hsub : ∀ x, Y x → X x) : FiniteSubset A Y := by
  have h := finiteSubset_induction A (fun X => ∀ Y, (∀ x, Y x → X x) → FiniteSubset A Y)
    (fun X he Y hsub => finiteSubset_empty A Y (fun x hy => he x (hsub x hy))) (by
      intro X Z a ha hi hf ih Y hsub
      obtain hya | hya := em (Y a)
      · have he : ∀ x, Y x ↔ (Y x ∧ x ≠ a) ∨ x = a := by
          intro x
          constructor
          · intro hy
            exact (em (x = a)).elim Or.inr (fun hn => Or.inl ⟨hy,hn⟩)
          · intro h
            exact h.elim (fun h => h.1) (fun e => e ▸ hya)
        exact finiteSubset_insert A (fun x => Y x ∧ x ≠ a) Y a ha he
          (ih _ (fun x h => ((hi x).mp (hsub x h.1)).elim id (fun e => (h.2 e).elim)))
      · exact ih Y (fun x hy => ((hi x).mp (hsub x hy)).elim id
          (fun e => (hya (e ▸ hy)).elim))) X hx
  exact h Y hsub

theorem finiteSubset_restrict (A X U : α → Prop) (hx : FiniteSubset A X) :
    FiniteSubset A (fun x => X x ∧ U x) := finiteSubset_subset A X _ hx (fun _ h => h.1)

theorem finiteSubset_mono (A B X : α → Prop) (hf : FiniteSubset A X)
    (h : ∀ x, A x → B x) : FiniteSubset B X :=
  hf (FiniteSubset B) (finiteSubset_empty B)
    (fun X Y a ha hi ih => finiteSubset_insert B X Y a (h a ha) hi ih)

theorem finiteSubset_rigid_representative (rc : P.RigidComprehension (α → Prop))
    (A X : α → Prop) (hf : FiniteSubset A X) :
    ∃ Y, RigidFinitePower A Y ∧ ∀ x, X x ↔ Y x := by
  obtain ⟨Y,hy,e⟩ := rc X
  exact ⟨Y,⟨hy,finiteSubset_coext A X Y hf e⟩,e⟩

theorem rigidFinitePower_sub_power (A : α → Prop) : ∀ X, RigidFinitePower A X → RigidPower A X :=
  fun X h => ⟨h.1,finiteSubset_members A X h.2⟩

theorem rigidFinitePower_embeds_power (A : α → Prop) : Embeds (RigidFinitePower A) (RigidPower A) :=
  embeds_of_subset _ _ (rigidFinitePower_sub_power A)

#classicism_check finiteSubset_empty finiteSubset_insert finiteSubset_induction finiteSubset_members finiteSubset_coext finiteSubset_singleton finiteSubset_union finiteSubset_subset finiteSubset_restrict finiteSubset_mono finiteSubset_rigid_representative rigidFinitePower_sub_power rigidFinitePower_embeds_power
#classicism_types finiteSubset_empty finiteSubset_insert finiteSubset_induction finiteSubset_members finiteSubset_coext finiteSubset_singleton finiteSubset_union finiteSubset_subset finiteSubset_restrict finiteSubset_mono finiteSubset_rigid_representative rigidFinitePower_sub_power rigidFinitePower_embeds_power
end Classicism.MathematicalContingency
