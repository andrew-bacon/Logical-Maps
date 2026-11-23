import Classicism.Results.MathematicalContingency.CountableBitSetup

/-! Both native forcing carriers have rigid ternary graphs as their elements.
Reuse the historical graph-coding result; no cardinal comparison is inferred
from coextension of arbitrary intensional predicates.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {α β γ δ σ τ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ] [Ty σ] [Ty τ]

theorem finiteCondition_embeds_power (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rc : P.RigidComprehension (δ → Prop))
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    Embeds (FiniteCondition A B D) (RigidPower J) :=
  embeds_trans _ (RigidTernaryPower A B D) _
    (embeds_of_subset _ _ (fun R h => ⟨h.1,finiteTernary_members A B D R h.2.1⟩))
    (rigidTernaryPower_embeds_of_pairing A B D J Q hq rc hA hB hD)

theorem countableBit_embeds_of_commonPairedBound (I J : τ → Prop)
    (common : CommonPairedBound (@LowerNat σ _) J)
    (sub : ∀ x, I x → J x) (rc : P.RigidComprehension (τ → Prop)) :
    Embeds (@CountableBitCarrier σ τ _ _ I) (RigidPower J) := by
  obtain ⟨_,Q,_,_,_,hq,_,_,_,hN,_,hBits⟩ := common
  exact countableCondition_embeds_power LowerNat LowerNat I ConditionBit J Q hq rc
    hN (embeds_of_subset I J sub) hBits

theorem cohen_embeds_of_commonPairedBound (I : τ → Prop)
    (common : CommonPairedBound (@LowerNat σ _) I)
    (rc : P.RigidComprehension (τ → Prop)) :
    Embeds (@CohenCondition σ τ _ _ I) (RigidPower I) := by
  obtain ⟨_,Q,_,_,_,hq,_,_,_,hN,hI,hBits⟩ := common
  exact finiteCondition_embeds_power LowerNat I ConditionBit I Q hq rc hN hI hBits

#classicism_check finiteCondition_embeds_power countableBit_embeds_of_commonPairedBound
  cohen_embeds_of_commonPairedBound
#classicism_types finiteCondition_embeds_power countableBit_embeds_of_commonPairedBound
  cohen_embeds_of_commonPairedBound
end Classicism.MathematicalContingency.FinitePower
