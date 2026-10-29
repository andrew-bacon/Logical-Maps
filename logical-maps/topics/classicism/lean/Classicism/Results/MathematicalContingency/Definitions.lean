import Classicism.Principles.Comprehension
import Classicism.Principles.Choice
import Classicism.Results.MathematicalContingency.Infinity

/-! Carrier-relative vocabulary; all maps are relations in the object language.
Reconstructed by OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
def Maps {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop :=
  (∀ x y, F x y → A x ∧ B y) ∧
  (∀ x, A x → ∃ y, B y ∧ F x y) ∧
  (∀ x y z, F x y → F x z → y = z)
def Injects {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop :=
  Maps F A B ∧ ∀ x z y, F x y → F z y → x = z
def Surjects {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop :=
  Maps F A B ∧ ∀ y, B y → ∃ x, A x ∧ F x y
def Bijects {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop := Injects F A B ∧ Surjects F A B
def Embeds {σ τ : Type} [Ty σ] [Ty τ] (A : σ → Prop) (B : τ → Prop) : Prop :=
  ∃ F, Injects F A B
def Smaller {σ τ : Type} [Ty σ] [Ty τ] (A : σ → Prop) (B : τ → Prop) : Prop :=
  Embeds A B ∧ ¬ Embeds B A
def Equinumerous {σ τ : Type} [Ty σ] [Ty τ] (A : σ → Prop) (B : τ → Prop) : Prop :=
  ∃ F, Bijects F A B
def RigidPower {σ : Type} [Ty σ] (A X : σ → Prop) : Prop :=
  Rigid X ∧ ∀ x, X x → A x
def StrictOrderOn {σ : Type} [Ty σ] (A : σ → Prop) (L : σ → σ → Prop) : Prop :=
  (∀ x y, L x y → A x ∧ A y) ∧
  (∀ x, A x → ¬ L x x) ∧
  (∀ x y z, A x → A y → A z → L x y → L y z → L x z) ∧
  (∀ x y, A x → A y → x = y ∨ L x y ∨ L y x)
def WellOrderOn {σ : Type} [Ty σ] (A : σ → Prop) (L : σ → σ → Prop) : Prop :=
  StrictOrderOn A L ∧ ∀ X : σ → Prop, (∀ x, X x → A x) → (∃ x, X x) →
    ∃ x, X x ∧ ∀ y, X y → ¬ L y x
def Segment {σ : Type} [Ty σ] (A : σ → Prop) (L : σ → σ → Prop) (a : σ) : σ → Prop :=
  fun x => A x ∧ L x a
def OrderIso {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (L : σ → σ → Prop) (B : τ → Prop) (M : τ → τ → Prop) : Prop :=
  Bijects F A B ∧ ∀ x y u v, F x u → F y v → (L x y ↔ M u v)
def PartialOrderOn {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) : Prop :=
  (∀ x y, E x y → A x ∧ A y) ∧ (∀ x, A x → E x x) ∧
  (∀ x y, E x y → E y x → x = y) ∧ (∀ x y z, E x y → E y z → E x z)
def Supremum {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop)
    (X : σ → Prop) (s : σ) : Prop :=
  A s ∧ (∀ x, X x → E x s) ∧ ∀ y, A y → (∀ x, X x → E x y) → E s y
def Infimum {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop)
    (X : σ → Prop) (s : σ) : Prop :=
  A s ∧ (∀ x, X x → E s x) ∧ ∀ y, A y → (∀ x, X x → E y x) → E y s
def Joins {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) (x y z : σ) : Prop :=
  Supremum A E (fun u => u = x ∨ u = y) z
def Meets {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) (x y z : σ) : Prop :=
  Infimum A E (fun u => u = x ∨ u = y) z
def Endpoints {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) (o i : σ) : Prop :=
  A o ∧ A i ∧ ∀ x, A x → E o x ∧ E x i
def DistributiveOn {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) : Prop :=
  ∀ x y z j l r s, A x → A y → A z → Joins A E y z j → Meets A E x j l →
    Meets A E x y r → Meets A E x z s → Joins A E r s l
def CBA {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) : Prop :=
  PartialOrderOn A E ∧
  (∀ X : σ → Prop, (∀ x, X x → A x) → ∃ s, Supremum A E X s) ∧
  (∀ X : σ → Prop, (∀ x, X x → A x) → ∃ s, Infimum A E X s) ∧
  DistributiveOn A E ∧ ∃ o i, Endpoints A E o i ∧
    ∀ x, A x → ∃ y, A y ∧ Meets A E x y o ∧ Joins A E x y i
def InitialCardinal {σ : Type} [Ty σ] (K : σ → Prop) (L : σ → σ → Prop) : Prop :=
  WellOrderOn K L ∧ ∀ a, K a → ¬ Embeds K (Segment K L a)
def RegularCardinal {σ : Type} [Ty σ] (K : σ → Prop) (L : σ → σ → Prop) : Prop :=
  ∀ X, (∀ x, X x → K x) → Smaller X K → ∃ a, K a ∧ ∀ x, X x → L x a
def StrongLimit {σ : Type} [Ty σ] (K : σ → Prop) (L : σ → σ → Prop) : Prop :=
  ∀ a, K a → ∃ b, K b ∧ Embeds (RigidPower (Segment K L a)) (Segment K L b)
def StronglyInaccessible {σ : Type} [Ty σ] (K : σ → Prop) (L : σ → σ → Prop) : Prop :=
  InitialCardinal K L ∧ Smaller (@LowerNat e _) K ∧ RegularCardinal K L ∧ StrongLimit K L
def Small {σ τ : Type} [Ty σ] [Ty τ] (K : σ → Prop) (L : σ → σ → Prop)
    (B : τ → Prop) : Prop := ∃ a, K a ∧ Embeds B (Segment K L a)
def Below (p q : Prop) : Prop := □ (q → p)
def EntailmentOrder (p q : Prop) : Prop := □ (p → q)
def MPAt (τ : Type) [Ty τ] {σ : Type} [Ty σ] (K : σ → Prop) (L : σ → σ → Prop) : Prop :=
  ∀ B E, CBA B E → Small K L B → ∃ p F, @OrderIso τ Prop _ _ F B E (Below p) EntailmentOrder
def BoxRC (τ : Type) [Rel τ] : Prop := P.NecRigidComprehension τ
def IC (σ : Type) [Ty σ] : Prop := P.IntensionalChoice σ
end Classicism.MathematicalContingency
