import Classicism.Results.MathematicalContingency.WellOrderPullback
import Classicism.Results.MathematicalContingency.PairingAbsorption
import Classicism.Results.MathematicalContingency.CohenConditions

/-!
Finite-condition well-orders from the existing relational cardinal bound.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The well-ordered paired bound and coordinate embeddings remain explicit.
No pending high-type Hartogs certificate is imported.
-/
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

theorem finiteCondition_wellOrder_of_pairing
    (A : α → Prop) (B : β → Prop) (D : γ → Prop) (J : δ → Prop)
    (Q : δ → δ → δ → Prop) (rc : P.RigidComprehension (δ → Prop))
    (L : δ → δ → Prop) (order : WellOrderOn J L) (pairing : PairingOn J Q)
    (a b : δ) (ha : J a) (hb : J b) (hne : a ≠ b)
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    ∃ LC, WellOrderOn (FiniteCondition A B D) LC :=
  wellOrder_exists_of_embeds (FiniteCondition A B D) J L order
    (finiteCondition_bound_of_pairing A B D J Q rc L order pairing a b ha hb hne hA hB hD)

theorem cohenCondition_wellOrder_of_pairing {σ : Type} [Ty σ]
    (I : β → Prop) (J : δ → Prop) (Q : δ → δ → δ → Prop)
    (rc : P.RigidComprehension (δ → Prop)) (L : δ → δ → Prop)
    (order : WellOrderOn J L) (pairing : PairingOn J Q)
    (a b : δ) (ha : J a) (hb : J b) (hne : a ≠ b)
    (naturals : Embeds (@LowerNat σ _) J) (indices : Embeds I J)
    (bits : Embeds ConditionBit J) :
    ∃ LC, WellOrderOn (@CohenCondition σ β _ _ I) LC :=
  finiteCondition_wellOrder_of_pairing LowerNat I ConditionBit J Q rc L order pairing
    a b ha hb hne naturals indices bits

#classicism_check finiteCondition_wellOrder_of_pairing cohenCondition_wellOrder_of_pairing
#classicism_types finiteCondition_wellOrder_of_pairing cohenCondition_wellOrder_of_pairing
end Classicism.MathematicalContingency
