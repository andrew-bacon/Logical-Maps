import Classicism.Results.MathematicalContingency.FrozenRowMaps
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]
def CharacteristicBits (A S : α → Prop) (n : α) (b : Prop) : Prop :=
  A n ∧ ((S n ∧ b = True) ∨ (¬ S n ∧ b = False))

theorem characteristicBits_maps (A S : α → Prop) : Maps (CharacteristicBits A S) A ConditionBit := by
  refine ⟨?_,?_,?_⟩
  · intro n b h
    exact ⟨h.1,h.2.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)⟩
  · intro n hn
    exact (em (S n)).elim
      (fun h => ⟨True,conditionBit_true,hn,Or.inl ⟨h,rfl⟩⟩)
      (fun h => ⟨False,conditionBit_false,hn,Or.inr ⟨h,rfl⟩⟩)
  · intro n b c hb hc
    obtain hb | hb := hb.2
    · exact hc.2.elim (fun hc => hb.2.trans hc.2.symm) (fun hc => (hc.1 hb.1).elim)
    · exact hc.2.elim (fun hc => (hb.1 hc.1).elim) (fun hc => hb.2.trans hc.2.symm)
#classicism_check characteristicBits_maps
#classicism_types characteristicBits_maps
end Classicism.MathematicalContingency
