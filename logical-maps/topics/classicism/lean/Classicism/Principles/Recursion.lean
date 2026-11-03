import Classicism.Background.ChurchSequences

/-!
# Church-numeral Infinity and functional recursion

Type parameters are schematic. Iteration carriers and output types are relational;
sequence entries may be individuals. Equations are restricted to the inductively
generated naturals/sequences. The map states the two implications from boxed
Church-numeral Infinity, with mathematical proofs in the associated write-ups.
No axiom, `sorry`, or claim of a derivation certificate is introduced here.
-/

namespace Classicism.P

/-- `church-numeral-infinity`: zero separation and injective natural successor. -/
def ChurchNumeralInfinity (α : Type) [Rel α] : Prop := Church.Infinity α

/-- `necessary-church-numeral-infinity`: box the whole Infinity sentence. -/
def NecChurchNumeralInfinity (α : Type) [Rel α] : Prop := □ (ChurchNumeralInfinity α)

/-- `church-numeral-functional-recursion`: recursion into every relational output type. -/
def ChurchNumeralFunctionalRecursion (α τ : Type) [Rel α] [Rel τ] : Prop :=
  ∀ (a : τ) (g : τ → τ), ∃ f : Church.Num α → τ,
    f (Church.zero α) = a ∧
    ∀ n, Church.Nat n → f (Church.suc n) = g (f n)

/-- `sequence-functional-recursion`: use accumulator `Church.Num α → Prop`. -/
def SequenceFunctionalRecursion (α σ τ : Type) [Rel α] [Ty σ] [Rel τ] : Prop :=
  ∀ (a : τ) (g : σ → τ → τ), ∃ f : Church.Seq α σ → τ,
    f (Church.nil α σ) = a ∧
    ∀ b s, Church.Finite s → f (Church.cons b s) = g b (f s)

end Classicism.P
