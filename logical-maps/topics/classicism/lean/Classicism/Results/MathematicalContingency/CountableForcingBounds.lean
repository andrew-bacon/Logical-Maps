import Classicism.Results.MathematicalContingency.CountableClosedBounds

namespace Classicism.MathematicalContingency
variable {κ ν α β γ δ ε : Type} [Ty κ] [Ty ν] [Ty α] [Ty β] [Ty γ] [Ty δ] [Ty ε]

theorem countableCondition_embeds_power (N : ν → Prop)
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop))
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    Embeds (CountableCondition N A B D) (RigidPower J) :=
  embeds_trans (CountableCondition N A B D) (RigidTernaryPower A B D) (RigidPower J)
    (embeds_of_subset _ _ (fun R h => ⟨h.1,h.2.1⟩))
    (rigidTernaryPower_embeds_of_pairing A B D J Q hq rcJ hA hB hD)

theorem countableCondition_small_of_pairing
    (K : κ → Prop) (L : κ → κ → Prop) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop))
    (N : ν → Prop) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    Small K L (CountableCondition N A B D) :=
  small_of_embeds_rigidPower K L limit rcK (CountableCondition N A B D) J
    (countableCondition_embeds_power N A B D J Q hq rcJ hA hB hD) small

theorem countableCondition_wellOrder_of_pairing
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (N : ν → Prop) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    ∃ LC, WellOrderOn (CountableCondition N A B D) LC :=
  small_wellOrder_exists K L hk (CountableCondition N A B D)
    (countableCondition_small_of_pairing K L limit rcK N A B D J Q hq rcJ small hA hB hD)

theorem countableCondition_completion_small
    (K : κ → Prop) (L : κ → κ → Prop) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop))
    (N : ν → Prop) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J)
    (rcConditions : P.RigidComprehension ((α → β → γ → Prop) → Prop))
    (H : ε → Prop) (R : ε → ε → Prop) (o : ε)
    (C : (α → β → γ → Prop) → ε → Prop)
    (cba : CBA H R) (member : H o) (least : ∀ b, H b → R o b)
    (cones : DenseCones (CountableCondition N A B D)
      (CountableConditionOrder N A B D) H R o C) : Small K L H :=
  denseCones_small K L limit rcK (CountableCondition N A B D)
    (CountableConditionOrder N A B D) H R o C cba member least cones
    (CountableCondition N A B D) rcConditions (embeds_refl _)
    (countableCondition_small_of_pairing K L limit rcK N A B D J Q hq rcJ small hA hB hD)

#classicism_check countableCondition_embeds_power countableCondition_small_of_pairing countableCondition_wellOrder_of_pairing countableCondition_completion_small
#classicism_types countableCondition_embeds_power countableCondition_small_of_pairing countableCondition_wellOrder_of_pairing countableCondition_completion_small
end Classicism.MathematicalContingency
