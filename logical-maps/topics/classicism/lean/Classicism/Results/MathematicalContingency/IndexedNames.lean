import Classicism.Results.MathematicalContingency.DecisionRepresentation
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α τ : Type} [Ty α] [Ty τ]

def IndexedName (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (a : τ) (X : α → Prop) : Prop := I a ∧ RepresentsOn A (T a) X

def NameCarrier (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (X : α → Prop) : Prop := ∃ a, IndexedName A I T a X

theorem indexedName_exists (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (rc : P.RigidComprehension (α → Prop → Prop)) (ha : Rigid A)
    (nd : ∀ x y, A x → A y → x ≠ y → □ (x ≠ y))
    (total : ∀ a n, I a → A n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → A n → T a n p → T a n q → p = q)
    (a : τ) (hia : I a) : ∃ X, IndexedName A I T a X := by
  obtain ⟨X,hX,_⟩ := restricted_name_representation rc A (T a) ha nd
    (fun n hn => total a n hia hn) (fun n hn p q hp hq => functional a n p q hia hn hp hq)
  exact ⟨X,hia,hX⟩

theorem indexedName_unique (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (ha : Rigid A) (total : ∀ a n, I a → A n → ∃ p, T a n p)
    (a : τ) (X Y : α → Prop) (hx : IndexedName A I T a X) (hy : IndexedName A I T a Y) : X = Y :=
  restricted_name_unique A (T a) ha (fun n hn => total a n hx.1 hn) X Y hx.2 hy.2

theorem indexedName_maps (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (ha : Rigid A) (total : ∀ a n, I a → A n → ∃ p, T a n p)
    (existsName : ∀ a, I a → ∃ X, IndexedName A I T a X) :
    Maps (IndexedName A I T) I (NameCarrier A I T) :=
  ⟨fun a X h => ⟨h.1,a,h⟩,
    fun a hi => (existsName a hi).elim (fun X hx => ⟨X,⟨a,hx⟩,hx⟩),
    fun a X Y hx hy => indexedName_unique A I T ha total a X Y hx hy⟩

theorem indexedName_bijects (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (ha : Rigid A) (total : ∀ a n, I a → A n → ∃ p, T a n p)
    (existsName : ∀ a, I a → ∃ X, IndexedName A I T a X)
    (separate : ∀ a b X Y, IndexedName A I T a X → IndexedName A I T b Y → a ≠ b → X ≠ Y) :
    Bijects (IndexedName A I T) I (NameCarrier A I T) := by
  have hm := indexedName_maps A I T ha total existsName
  refine ⟨⟨hm,?_⟩,hm,?_⟩
  · intro a b X ha hb
    exact (em (a = b)).elim id (fun hn => (separate a b X X ha hb hn rfl).elim)
  · intro X hx
    obtain ⟨a,ha⟩ := hx
    exact ⟨a,ha.1,ha⟩

#classicism_check indexedName_exists indexedName_unique indexedName_maps indexedName_bijects
#classicism_types indexedName_exists indexedName_unique indexedName_maps indexedName_bijects
end Classicism.MathematicalContingency
