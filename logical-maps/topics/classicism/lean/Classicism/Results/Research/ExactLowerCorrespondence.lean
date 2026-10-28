import Classicism.Cardinality
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem

/-!
# Exact and at-least finite cardinalities

Both systems use the same cardinal successor, but have different zeros.
The graph `ExactLowerPair` is generated synchronously from these zeros.
Under the Peano separation properties for BOTH presentations, its graph
is a bijection of their impredicatively defined finite-cardinality carriers.

No natural-number type, choice function, or primitive numeral index occurs in
the statement. The graph is definable in the relational language of Classicism.
The hypotheses cannot simply be omitted in the proof below: the remaining
exact-Peano comparison from the lower-Peano hypothesis is a separate task.
-/
namespace Classicism.ExactLower

variable {σ : Type} [Ty σ]

/-- Zero and inductive carrier for at-least counts, in the map's own vocabulary. -/
def AtLeastZero (σ : Type) [Ty σ] : (σ → Prop) → Prop := fun _ => True

def LowerNat (l : (σ → Prop) → Prop) : Prop :=
  ∀ Z : ((σ → Prop) → Prop) → Prop,
    (Z (AtLeastZero σ) ∧ ∀ n, Z n → Z (SucCard n)) → Z l

def LowerPeano (σ : Type) [Ty σ] : Prop :=
  (∀ n, LowerNat n → AtLeastZero σ ≠ SucCard n) ∧
  (∀ m n : (σ → Prop) → Prop,
    LowerNat m → LowerNat n → SucCard m = SucCard n → m = n)

/-- The boxed version of the at-least Peano conditions. -/
def NecessaryLowerPeano (σ : Type) [Ty σ] : Prop := □ (LowerPeano σ)

theorem lowerNat_zero : LowerNat (AtLeastZero σ) := fun _ h => h.1

theorem lowerNat_suc (l : (σ → Prop) → Prop) (hl : LowerNat l) :
    LowerNat (SucCard l) := fun Z hz => hz.2 l (hl Z hz)

/-- Peano's zero and successor separation for the *exact* finite counts. -/
def ExactPeano (σ : Type) [Ty σ] : Prop :=
  (∀ n : (σ → Prop) → Prop, FiniteCardinality n → ZeroCard σ ≠ SucCard n) ∧
  (∀ m n : (σ → Prop) → Prop,
    FiniteCardinality m → FiniteCardinality n →
    SucCard m = SucCard n → m = n)

/-- The inductively generated *relation*, pairing the two zeros and
    relating the successors of every pair. -/
def ExactLowerPair (e l : (σ → Prop) → Prop) : Prop :=
  ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop,
    (R (ZeroCard σ) (AtLeastZero σ) ∧
      ∀ x y, R x y → R (SucCard x) (SucCard y)) → R e l

theorem exactLowerPair_zero :
    ExactLowerPair (ZeroCard σ) (AtLeastZero σ) :=
  fun _ h => h.1

theorem exactLowerPair_suc (e l : (σ → Prop) → Prop)
    (h : ExactLowerPair e l) :
    ExactLowerPair (SucCard e) (SucCard l) :=
  fun R hr => hr.2 e l (h R hr)

theorem exactLowerPair_exact (e l : (σ → Prop) → Prop)
    (h : ExactLowerPair e l) : FiniteCardinality e :=
  h (fun x _ => FiniteCardinality x)
    ⟨finiteCardinality_zero, fun x _ hx => finiteCardinality_suc x hx⟩

theorem exactLowerPair_lower (e l : (σ → Prop) → Prop)
    (h : ExactLowerPair e l) : LowerNat l :=
  h (fun _ y => LowerNat y)
    ⟨lowerNat_zero, fun _ y hy => lowerNat_suc y hy⟩

/-- Every paired item is either the pair of zeros or a pair of successors
    of an earlier paired item. -/
theorem exactLowerPair_cases (e l : (σ → Prop) → Prop)
    (h : ExactLowerPair e l) :
    (e = ZeroCard σ ∧ l = AtLeastZero σ) ∨
      ∃ x y, ExactLowerPair x y ∧ e = SucCard x ∧ l = SucCard y := by
  have hh := h (fun x y => ExactLowerPair x y ∧
    ((x = ZeroCard σ ∧ y = AtLeastZero σ) ∨
      ∃ a b, ExactLowerPair a b ∧ x = SucCard a ∧ y = SucCard b))
    ⟨⟨exactLowerPair_zero, Or.inl ⟨rfl, rfl⟩⟩,
      fun x y hxy => ⟨exactLowerPair_suc x y hxy.1,
        Or.inr ⟨x, y, hxy.1, rfl, rfl⟩⟩⟩
  exact hh.2

/-- Every exact finite cardinality has an at-least partner. -/
theorem exactLowerPair_total_exact (e : (σ → Prop) → Prop)
    (he : FiniteCardinality e) : ∃ l, ExactLowerPair e l :=
  he (fun x => ∃ l, ExactLowerPair x l)
    ⟨⟨AtLeastZero σ, exactLowerPair_zero⟩,
      fun x hx => hx.elim fun l hxl =>
        ⟨SucCard l, exactLowerPair_suc x l hxl⟩⟩

/-- Every at-least finite cardinality has an exact partner. -/
theorem exactLowerPair_total_lower (l : (σ → Prop) → Prop)
    (hl : LowerNat l) : ∃ e, ExactLowerPair e l :=
  hl (fun y => ∃ e, ExactLowerPair e y)
    ⟨⟨ZeroCard σ, exactLowerPair_zero⟩,
      fun y hy => hy.elim fun e hey =>
        ⟨SucCard e, exactLowerPair_suc e y hey⟩⟩

/-- Functionality: under the exact Peano condition, an exact count
    cannot have two different at-least partners. -/
theorem exactLowerPair_right_unique (hp : ExactPeano σ)
    (e l : (σ → Prop) → Prop) (h : ExactLowerPair e l) :
    ∀ l', ExactLowerPair e l' → l' = l := by
  have hh := h (fun x y => ExactLowerPair x y ∧
      ∀ z, ExactLowerPair x z → z = y)
    ⟨⟨exactLowerPair_zero,
        fun z hz => by
          rcases exactLowerPair_cases (ZeroCard σ) z hz with ⟨_, heq⟩ | ⟨a, b, hab, heq, _⟩
          · exact heq
          · exact False.elim (hp.1 a (exactLowerPair_exact a b hab) heq)⟩,
      fun x y ih =>
        ⟨exactLowerPair_suc x y ih.1,
          fun z hz => by
            rcases exactLowerPair_cases (SucCard x) z hz with ⟨heq, _⟩ | ⟨a, b, hab, heq, hz'⟩
            · exact False.elim (hp.1 x (exactLowerPair_exact x y ih.1) heq.symm)
            · have hxa : x = a := hp.2 x a
                (exactLowerPair_exact x y ih.1) (exactLowerPair_exact a b hab) heq
              have hba : b = y := ih.2 b (by simpa only [← hxa] using hab)
              exact hz'.trans (congrArg SucCard hba)⟩⟩
  exact hh.2

/-- Injectivity: under the at-least Peano condition, two exact
    cardinalities paired with the same at-least count coincide. -/
theorem exactLowerPair_left_unique (hp : LowerPeano σ)
    (e l : (σ → Prop) → Prop) (h : ExactLowerPair e l) :
    ∀ e', ExactLowerPair e' l → e' = e := by
  have hh := h (fun x y => ExactLowerPair x y ∧
      ∀ z, ExactLowerPair z y → z = x)
    ⟨⟨exactLowerPair_zero,
        fun z hz => by
          rcases exactLowerPair_cases z (AtLeastZero σ) hz with ⟨heq, _⟩ | ⟨a, b, hab, _, heq⟩
          · exact heq
          · exact False.elim (hp.1 b (exactLowerPair_lower a b hab) heq)⟩,
      fun x y ih =>
        ⟨exactLowerPair_suc x y ih.1,
          fun z hz => by
            rcases exactLowerPair_cases z (SucCard y) hz with ⟨_, heq⟩ | ⟨a, b, hab, hz', heq⟩
            · exact False.elim (hp.1 y (exactLowerPair_lower x y ih.1) heq.symm)
            · have hyb : y = b := hp.2 y b
                (exactLowerPair_lower x y ih.1) (exactLowerPair_lower a b hab) heq
              have hax : a = x := ih.2 a (by simpa only [← hyb] using hab)
              exact hz'.trans (congrArg SucCard hax)⟩⟩
  exact hh.2

/-- The exact and at-least cardinality carriers admit a relation which
    is total and injective in both directions (an object-language bijection). -/
def ExactLowerBijection (σ : Type) [Ty σ] : Prop :=
  ∃ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop,
    (∀ e l, R e l → FiniteCardinality e ∧ LowerNat l) ∧
    (∀ e, FiniteCardinality e → ∃ l, R e l) ∧
    (∀ l, LowerNat l → ∃ e, R e l) ∧
    (∀ e l l', R e l → R e l' → l = l') ∧
    (∀ e e' l, R e l → R e' l → e = e') ∧
    R (ZeroCard σ) (AtLeastZero σ) ∧
    (∀ e l, R e l → R (SucCard e) (SucCard l))

/-- Main result. Neither a function term nor a natural-number carrier
    is assumed to exist: the bijection is witnessed by a binary relation. -/
theorem exactLowerBijection_of_peano
    (he : ExactPeano σ) (hl : LowerPeano σ) :
    ExactLowerBijection σ := by
  refine ⟨ExactLowerPair, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e l h
    exact ⟨exactLowerPair_exact e l h, exactLowerPair_lower e l h⟩
  · exact exactLowerPair_total_exact
  · exact exactLowerPair_total_lower
  · intro e l l' h h'
    exact (exactLowerPair_right_unique he e l h l' h').symm
  · intro e e' l h h'
    exact (exactLowerPair_left_unique hl e l h e' h').symm
  · exact exactLowerPair_zero
  · intro e l h
    exact exactLowerPair_suc e l h

/-- In the intended CH setting, the at-least Peano hypothesis is boxed. -/
theorem exactLowerBijection_of_necessary_lower_peano
    (he : ExactPeano σ) (hl : NecessaryLowerPeano σ) :
    ExactLowerBijection σ :=
  exactLowerBijection_of_peano he (box_elim hl)

#classicism_check exactLowerPair_zero exactLowerPair_suc exactLowerPair_exact
  exactLowerPair_lower exactLowerPair_cases exactLowerPair_total_exact
  exactLowerPair_total_lower exactLowerPair_right_unique
  exactLowerPair_left_unique exactLowerBijection_of_peano
  exactLowerBijection_of_necessary_lower_peano
#classicism_types exactLowerPair_zero exactLowerPair_suc exactLowerPair_exact
  exactLowerPair_lower exactLowerPair_cases exactLowerPair_total_exact
  exactLowerPair_total_lower exactLowerPair_right_unique
  exactLowerPair_left_unique exactLowerBijection_of_peano
  exactLowerBijection_of_necessary_lower_peano
end Classicism.ExactLower
