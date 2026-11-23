import Classicism.Results.MathematicalContingency.PairedStages
import Classicism.Results.MathematicalContingency.IndexCardinality
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]
def CommonPairedBound (A : α → Prop) (J : β → Prop) : Prop :=
  ∃ L Q u v, WellOrderOn J L ∧ PairingOn J Q ∧ J u ∧ J v ∧ u ≠ v ∧
    Embeds A J ∧ Embeds J J ∧ Embeds ConditionBit J

theorem commonPairedBound_of_pairing (A : α → Prop) (J : β → Prop)
    (L : β → β → Prop) (hw : WellOrderOn J L) (pair : ∃ Q, PairingOn J Q)
    (embed : Embeds A J) (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b) :
    CommonPairedBound A J := by
  obtain ⟨Q,hq⟩ := pair
  obtain ⟨u,v,hu,hv,huv⟩ := embeds_preserves_two A J embed a b ha hb hne
  exact ⟨L,Q,u,v,hw,hq,hu,hv,huv,embed,embeds_refl J,conditionBit_embeds_two J u v hu hv huv⟩
#classicism_check commonPairedBound_of_pairing
#classicism_types commonPairedBound_of_pairing
end Classicism.MathematicalContingency
