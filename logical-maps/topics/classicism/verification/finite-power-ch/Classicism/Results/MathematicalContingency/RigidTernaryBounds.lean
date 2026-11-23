import Classicism.Results.MathematicalContingency.RigidTernaryCoding
import Classicism.Results.MathematicalContingency.SmallnessTransfer
import Classicism.Results.MathematicalContingency.WellOrderPullback

namespace Classicism.MathematicalContingency
variable {κ α β γ δ : Type} [Ty κ] [Ty α] [Ty β] [Ty γ] [Ty δ]

theorem small_wellOrder_exists (K : κ → Prop) (L : κ → κ → Prop)
    (hk : WellOrderOn K L) (A : α → Prop) (small : Small K L A) :
    ∃ R, WellOrderOn A R := by
  obtain ⟨a,ha,bound⟩ := small
  exact wellOrder_exists_of_embeds A (Segment K L a) (RestrictOrder L (Segment K L a))
    (wellOrder_restrict K (Segment K L a) L hk (fun _ h => h.1)) bound

theorem rigidTernaryPower_small_of_pairing
    (K : κ → Prop) (L : κ → κ → Prop) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop))
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    Small K L (RigidTernaryPower A B D) :=
  small_of_embeds_rigidPower K L limit rcK (RigidTernaryPower A B D) J
    (rigidTernaryPower_embeds_of_pairing A B D J Q hq rcJ hA hB hD) small

theorem rigidTernaryPower_wellOrder_of_pairing
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    ∃ R, WellOrderOn (RigidTernaryPower A B D) R :=
  small_wellOrder_exists K L hk (RigidTernaryPower A B D)
    (rigidTernaryPower_small_of_pairing K L limit rcK A B D J Q hq rcJ small hA hB hD)

#classicism_check small_wellOrder_exists rigidTernaryPower_small_of_pairing rigidTernaryPower_wellOrder_of_pairing
#classicism_types small_wellOrder_exists rigidTernaryPower_small_of_pairing rigidTernaryPower_wellOrder_of_pairing
end Classicism.MathematicalContingency
