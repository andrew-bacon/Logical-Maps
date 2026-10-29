import Classicism.Results.MathematicalContingency.RigidDomainCodes

namespace Classicism.MathematicalContingency
variable {κ σ α β γ δ : Type} [Ty κ] [Ty σ] [Ty α] [Ty β] [Ty γ] [Ty δ]

/-- The code-space premise is derived from small paired coordinate bounds and RC. -/
theorem countableCondition_countablyClosed_of_small_pairing
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (hp : LowerPeano σ) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hN : Embeds (@LowerNat σ _) J)
    (rcCode : P.RigidComprehension (α → β → ((σ → Prop) → Prop) → Prop))
    (rcGraph : P.RigidComprehension (α → β → γ → Prop)) :
    @CountablyClosed σ (α → β → γ → Prop) _ _
      (CountableCondition (@LowerNat σ _) A B D)
      (CountableConditionOrder (@LowerNat σ _) A B D) := by
  obtain ⟨LC,hw,available⟩ := countableCondition_wellOrdered_codes K L hk limit rcK
    LowerNat A B D J Q hq rcJ small hA hB hN rcCode
  exact countableCondition_countablyClosed_of_codes hp A B D (RigidTernaryPower A B LowerNat)
    LC hw available rcGraph

#classicism_check countableCondition_countablyClosed_of_small_pairing
#classicism_types countableCondition_countablyClosed_of_small_pairing
end Classicism.MathematicalContingency
