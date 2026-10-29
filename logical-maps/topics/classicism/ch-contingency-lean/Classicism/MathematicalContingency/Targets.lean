import Classicism.MathematicalContingency.Definitions
/-! Relational real structures and CH targets. These are definitions, not existence proofs.
Reconstructed by OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]
def BinaryOperationOn (R : σ → Prop) (A : σ → σ → σ → Prop) : Prop :=
  (∀ x y z, A x y z → R x ∧ R y ∧ R z) ∧
  (∀ x y, R x → R y → ∃ z, R z ∧ A x y z) ∧
  ∀ x y z w, A x y z → A x y w → z = w

def CommutativeOn (R : σ → Prop) (A : σ → σ → σ → Prop) : Prop :=
  ∀ x y z, R x → R y → R z → (A x y z ↔ A y x z)
def AssociativeOn (R : σ → Prop) (A : σ → σ → σ → Prop) : Prop :=
  ∀ x y z u v w, R x → R y → R z → A x y u → A y z v → (A u z w ↔ A x v w)
def NaturalPart (R : σ → Prop) (A : σ → σ → σ → Prop) (o i : σ) (n : σ) : Prop :=
  R n ∧ ∀ X : σ → Prop, X o →
    (∀ x y, R x → R y → X x → A x i y → X y) → X n

def OrderedFieldOn (R : σ → Prop) (A M : σ → σ → σ → Prop)
    (L : σ → σ → Prop) (o i : σ) : Prop :=
  R o ∧ R i ∧ o ≠ i ∧ BinaryOperationOn R A ∧ BinaryOperationOn R M ∧
  CommutativeOn R A ∧ CommutativeOn R M ∧ AssociativeOn R A ∧ AssociativeOn R M ∧
  (∀ x, R x → A x o x ∧ M x i x) ∧
  (∀ x, R x → ∃ y, R y ∧ A x y o) ∧
  (∀ x, R x → x ≠ o → ∃ y, R y ∧ M x y i) ∧
  (∀ x y z s u v w, R x → R y → R z → A y z s → M x y u → M x z v →
    (M x s w ↔ A u v w)) ∧
  StrictOrderOn R L ∧ L o i ∧
  (∀ x y z u v, R z → L x y → A x z u → A y z v → L u v) ∧
  ∀ x y z, L o x → L o y → M x y z → L o z

def CompleteOn (R : σ → Prop) (L : σ → σ → Prop) : Prop :=
  ∀ X : σ → Prop, (∀ x, X x → R x) → (∃ x, X x) →
    (∃ b, R b ∧ ∀ x, X x → x = b ∨ L x b) →
    ∃ s, Supremum R (fun x y => R x ∧ R y ∧ (x = y ∨ L x y)) X s

def RealStructure (R : σ → Prop) (A M : σ → σ → σ → Prop)
    (L : σ → σ → Prop) (o i : σ) : Prop :=
  OrderedFieldOn R A M L o i ∧ CompleteOn R L ∧
    ∀ x, R x → ∃ n, NaturalPart R A o i n ∧ L x n

def CH (R : σ → Prop) (A : σ → σ → σ → Prop) (o i : σ) : Prop :=
  ∀ X : σ → Prop, (∀ x, X x → R x) →
    Embeds X (NaturalPart R A o i) ∨ Equinumerous X R

def HasReals (σ : Type) [Ty σ] : Prop :=
  ∃ R A M L o i, @RealStructure σ _ R A M L o i
def NecessaryReals (σ : Type) [Ty σ] : Prop := □ (HasReals σ)
def PossibleCH (σ : Type) [Ty σ] : Prop :=
  ◇ (∃ R A M L o i, @RealStructure σ _ R A M L o i ∧ CH R A o i)
def PossibleNotCH (σ : Type) [Ty σ] : Prop :=
  ◇ (∃ R A M L o i, @RealStructure σ _ R A M L o i ∧ ¬ CH R A o i)
def CHContingency (σ : Type) [Ty σ] : Prop := PossibleCH σ ∧ PossibleNotCH σ

/-- A finite collection of instances of MP, sharing an inaccessible bound.
This is not a quantification over object-language types. -/
def TwoAlgebraCoverage (κ σ τ : Type) [Ty κ] [Ty σ] [Ty τ] : Prop :=
  ∃ K : κ → Prop, ∃ L : κ → κ → Prop,
    StronglyInaccessible K L ∧ MPAt σ K L ∧ MPAt τ K L

/-- A selected instance package. BoxRC and IC must additionally be instantiated at
every auxiliary relational type used by a completed proof. -/
def AssumptionsAt (ν κ σ τ ρ : Type) [Ty ν] [Ty κ] [Ty σ] [Ty τ] [Rel ρ] : Prop :=
  DraftBoxInfinity ν ∧ BoxRC ρ ∧ IC ρ ∧ TwoAlgebraCoverage κ σ τ

/-- Statement only: the missing higher-type Dedekind construction is not installed as an axiom. -/
def NecessaryRealsObligation (ν η : Type) [Ty ν] [Ty η] : Prop :=
  DraftBoxInfinity ν → NecessaryReals η
end Classicism.MathematicalContingency
