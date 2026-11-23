import Classicism.Results.MathematicalContingency.CommonPairedBound
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]
theorem commonPairedBound_of_nontrivial (A : α → Prop) (J : β → Prop)
    (L : β → β → Prop) (hw : WellOrderOn J L) (pair : ∃ Q, PairingOn J Q)
    (embed : Embeds A J) (two : ∃ a b, A a ∧ A b ∧ a ≠ b) : CommonPairedBound A J := by
  obtain ⟨a,b,ha,hb,hne⟩ := two
  exact commonPairedBound_of_pairing A J L hw pair embed a b ha hb hne
#classicism_check commonPairedBound_of_nontrivial
#classicism_types commonPairedBound_of_nontrivial
end Classicism.MathematicalContingency
