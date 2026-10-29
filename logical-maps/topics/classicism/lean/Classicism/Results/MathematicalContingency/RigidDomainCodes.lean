import Classicism.Results.MathematicalContingency.RigidTernaryBounds
import Classicism.Results.MathematicalContingency.CountableSequenceClosure

namespace Classicism.MathematicalContingency
variable {κ ν α β γ δ : Type} [Ty κ] [Ty ν] [Ty α] [Ty β] [Ty γ] [Ty δ]

theorem countableDomain_rigid_code (N : ν → Prop) (R : α → β → γ → Prop)
    (rc : P.RigidComprehension (α → β → ν → Prop)) (hr : CountableDomain N R) :
    ∃ C, Rigid C ∧ CountableDomainCode N R C := by
  obtain ⟨F,hF⟩ := hr
  obtain ⟨C,hC,e⟩ := rc F
  exact ⟨C,hC,countableDomainCode_coext N R F C hF e⟩

theorem countableCondition_rigid_code (N : ν → Prop) (A : α → Prop)
    (B : β → Prop) (D : γ → Prop)
    (rc : P.RigidComprehension (α → β → ν → Prop))
    (R : α → β → γ → Prop) (hr : CountableCondition N A B D R) :
    ∃ C, RigidTernaryPower A B N C ∧ CountableDomainCode N R C := by
  obtain ⟨C,hC,hcode⟩ := countableDomain_rigid_code N R rc hr.2.2.1
  refine ⟨C,⟨hC,?_⟩,hcode⟩
  intro x y n h
  obtain ⟨hn,z,hz⟩ := hcode.1 x y n h
  exact ⟨(hr.2.1 x y z hz).1,(hr.2.1 x y z hz).2.1,hn⟩

theorem countableCondition_wellOrdered_codes
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (N : ν → Prop) (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rcJ : P.RigidComprehension (δ → Prop)) (small : Small K L J)
    (hA : Embeds A J) (hB : Embeds B J) (hN : Embeds N J)
    (rcCode : P.RigidComprehension (α → β → ν → Prop)) :
    ∃ LC, WellOrderOn (RigidTernaryPower A B N) LC ∧
      ∀ R, CountableCondition N A B D R →
        ∃ C, RigidTernaryPower A B N C ∧ CountableDomainCode N R C := by
  obtain ⟨LC,hLC⟩ := rigidTernaryPower_wellOrder_of_pairing K L hk limit rcK A B N
    J Q hq rcJ small hA hB hN
  exact ⟨LC,hLC,countableCondition_rigid_code N A B D rcCode⟩

#classicism_check countableDomain_rigid_code countableCondition_rigid_code countableCondition_wellOrdered_codes
#classicism_types countableDomain_rigid_code countableCondition_rigid_code countableCondition_wellOrdered_codes
end Classicism.MathematicalContingency
