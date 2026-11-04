import Classicism.Background.Necessity

/-!
# Church numerals and sequences

Andrew Bacon's *Notes for Zach* (25 March 2023), §§1–3, is the background source.
These numerals are distinct from the Fregean cardinalities in `Arithmetic.lean`.
The sequence accumulator is `Num α → Prop`, rather than the note's `Prop`.
This change makes the positional-observation proof of constructor injectivity
available from Church-numeral Infinity, without assuming sequence recursion.

The functional recursion principles are in `Principles/Recursion.lean`. The
map's two recursion implications have mathematical write-ups; this module does
not assert that those implications have derivation certificates.
-/

namespace Classicism.Church

/-- The Church numeral type, with relational iteration carrier `α`. -/
abbrev Num (α : Type) := (α → α) → α → α

/-- Zero, matching the 2023 note. -/
def zero (α : Type) [Rel α] : Num α := λ _ x ↦ x

/-- Right-iteration successor, matching the 2023 note. -/
def suc {α : Type} [Rel α] (n : Num α) : Num α := λ h x ↦ n h (h x)

/-- The least property containing zero and closed under successor. -/
def Nat {α : Type} [Rel α] (n : Num α) : Prop :=
  ∀ P : Num α → Prop, (P (zero α) ∧ ∀ m, P m → P (suc m)) → P n

/-- Peano separation for Church naturals, not the map's cardinality axiom. -/
def Infinity (α : Type) [Rel α] : Prop :=
  (∀ n : Num α, Nat n → suc n ≠ zero α) ∧
  ∀ m n : Num α, Nat m → Nat n → suc m = suc n → m = n

/-- The least numerical recursion relation. -/
def NumGraph {α τ : Type} [Rel α] [Rel τ] (a : τ) (g : τ → τ)
    (n : Num α) (x : τ) : Prop :=
  ∀ R : Num α → τ → Prop,
    (R (zero α) a ∧ ∀ m y, R m y → R (suc m) (g y)) → R n x

/-- Positional truth-value observations are the sequence accumulator. -/
abbrev Acc (α : Type) := Num α → Prop

/-- Church sequences of `σ`, using accumulator `Num α → Prop`. -/
abbrev Seq (α σ : Type) := (σ → Acc α → Acc α) → Acc α → Acc α

/-- The empty Church sequence. -/
def nil (α σ : Type) [Rel α] [Ty σ] : Seq α σ := λ _ z ↦ z

/-- Prefix one element. -/
def cons {α σ : Type} [Rel α] [Ty σ] (b : σ) (s : Seq α σ) : Seq α σ :=
  λ h z ↦ h b (s h z)

/-- The least property containing `nil` and closed under every prefix operation. -/
def Finite {α σ : Type} [Rel α] [Ty σ] (s : Seq α σ) : Prop :=
  ∀ P : Seq α σ → Prop,
    (P (nil α σ) ∧ ∀ b r, P r → P (cons b r)) → P s

/-- The least sequence recursion relation. -/
def SeqGraph {α σ τ : Type} [Rel α] [Ty σ] [Rel τ]
    (a : τ) (g : σ → τ → τ) (s : Seq α σ) (x : τ) : Prop :=
  ∀ R : Seq α σ → τ → Prop,
    (R (nil α σ) a ∧ ∀ b r y, R r y → R (cons b r) (g b y)) → R s x

/-- Prepend the truth value of `P b` to an array indexed by Church naturals. -/
def observeStep {α σ : Type} [Rel α] [Ty σ]
    (P : σ → Prop) (b : σ) (A : Acc α) : Acc α :=
  λ n ↦ (n = zero α ∧ P b) ∨ ∃ m, Nat m ∧ n = suc m ∧ A m

/-- Observation by Church application; no sequence recursor is assumed. -/
def observe {α σ : Type} [Rel α] [Ty σ]
    (P : σ → Prop) (s : Seq α σ) : Acc α :=
  s (observeStep P) (λ _ ↦ False)

/-- Agreement of every property observation at every natural position. -/
def SameObservations {α σ : Type} [Rel α] [Ty σ] (s r : Seq α σ) : Prop :=
  ∀ P : σ → Prop, ∀ n, Nat n → (observe P s n ↔ observe P r n)

section basic
variable {α σ : Type} [Rel α] [Ty σ]

theorem nat_zero : Nat (zero α) := fun _ h ↦ h.1

theorem nat_suc {n : Num α} (hn : Nat n) : Nat (suc n) :=
  fun P h ↦ h.2 n (hn P h)

theorem finite_nil : Finite (nil α σ) := fun _ h ↦ h.1

theorem finite_cons (b : σ) {s : Seq α σ} (hs : Finite s) : Finite (cons b s) :=
  fun P h ↦ h.2 b s (hs P h)

/-- Every generated sequence is empty or a cons of a generated sequence. -/
theorem finite_cases {s : Seq α σ} (hs : Finite s) :
    s = nil α σ ∨ ∃ b r, Finite r ∧ s = cons b r :=
  hs (λ s ↦ Finite s ∧ (s = nil α σ ∨ ∃ b r, Finite r ∧ s = cons b r))
    ⟨⟨finite_nil, Or.inl rfl⟩,
      fun b r h ↦ ⟨finite_cons b h.1, Or.inr ⟨b, r, h.1, rfl⟩⟩⟩ |>.2

theorem observe_nil (P : σ → Prop) (n : Num α) :
    observe P (nil α σ) n ↔ False := Iff.rfl

/-- Infinity's nonzero clause excludes a predecessor of zero. -/
theorem observe_cons_zero (hI : Infinity α) (P : σ → Prop) (b : σ) (s : Seq α σ) :
    observe P (cons b s) (zero α) ↔ P b := by
  constructor
  · intro h
    rcases h with h | ⟨m, hm, he, _⟩
    · exact h.2
    · exact False.elim (hI.1 m hm he.symm)
  · intro h
    exact Or.inl ⟨rfl, h⟩

/-- Infinity's two clauses recover the tail at successor positions. -/
theorem observe_cons_suc (hI : Infinity α) (P : σ → Prop) (b : σ) (s : Seq α σ)
    (n : Num α) (hn : Nat n) :
    observe P (cons b s) (suc n) ↔ observe P s n := by
  constructor
  · intro h
    rcases h with h | ⟨m, hm, he, hv⟩
    · exact False.elim (hI.1 n hn h.1)
    · exact (hI.2 n m hn hm he).symm ▸ hv
  · intro h
    exact Or.inr ⟨n, hn, rfl, h⟩

/-- Property observations distinguish generated sequences; no recursion theorem is used. -/
theorem sameObservations_eq (hI : Infinity α) {s : Seq α σ} (hs : Finite s) :
    ∀ r, Finite r → SameObservations s r → s = r := by
  apply hs (λ s ↦ ∀ r, Finite r → SameObservations s r → s = r)
  constructor
  · intro r hr he
    rcases finite_cases hr with h | ⟨c, v, _, h⟩
    · exact h.symm
    · subst r
      have hc := (observe_cons_zero hI (λ _ : σ ↦ True) c v).2 True.intro
      exact False.elim ((he (λ _ : σ ↦ True) (zero α) nat_zero).2 hc)
  · intro b s ih r hr he
    rcases finite_cases hr with h | ⟨c, v, hv, h⟩
    · subst r
      have hb := (observe_cons_zero hI (λ _ : σ ↦ True) b s).2 True.intro
      exact False.elim ((he (λ _ : σ ↦ True) (zero α) nat_zero).1 hb)
    · subst r
      have hbc : b = c := by
        have hb := (observe_cons_zero hI (λ x ↦ b = x) b s).2 rfl
        exact (observe_cons_zero hI (λ x ↦ b = x) c v).1
          ((he (λ x ↦ b = x) (zero α) nat_zero).1 hb)
      have htail : SameObservations s v := by
        intro P n hn
        exact (observe_cons_suc hI P b s n hn).symm.trans
          ((he P (suc n) (nat_suc hn)).trans (observe_cons_suc hI P c v n hn))
      have hsv := ih v hv htail
      exact congrArg (λ x ↦ cons x s) hbc |>.trans (congrArg (cons c) hsv)

/-- Cons is injective on the inductively generated sequences, from unboxed Infinity. -/
theorem cons_injective (hI : Infinity α) (b c : σ) (s r : Seq α σ)
    (hs : Finite s) (hr : Finite r) (he : cons b s = cons c r) : b = c ∧ s = r := by
  have ho : SameObservations (cons b s) (cons c r) := by
    intro P n _
    exact ⟨fun h ↦ (congrArg (λ z ↦ observe P z n) he).mp h,
      fun h ↦ (congrArg (λ z ↦ observe P z n) he).mpr h⟩
  have hbc : b = c := by
    have hb := (observe_cons_zero hI (λ x ↦ b = x) b s).2 rfl
    exact (observe_cons_zero hI (λ x ↦ b = x) c r).1
      ((ho (λ x ↦ b = x) (zero α) nat_zero).1 hb)
  have ht : SameObservations s r := by
    intro P n hn
    exact (observe_cons_suc hI P b s n hn).symm.trans
      ((ho P (suc n) (nat_suc hn)).trans (observe_cons_suc hI P c r n hn))
  exact ⟨hbc, sameObservations_eq hI hs r hr ht⟩

/-- A cons is never empty; this even holds without a generated-tail assumption. -/
theorem cons_ne_nil (hI : Infinity α) (b : σ) (s : Seq α σ) : cons b s ≠ nil α σ := by
  intro he
  have hb := (observe_cons_zero hI (λ _ : σ ↦ True) b s).2 True.intro
  exact False.elim ((congrArg (λ z ↦ observe (λ _ : σ ↦ True) z (zero α)) he).mp hb)

end basic
end Classicism.Church
