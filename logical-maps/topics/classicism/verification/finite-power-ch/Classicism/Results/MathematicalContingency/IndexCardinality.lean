import Classicism.Results.MathematicalContingency.HartogsPairing
import Classicism.Results.MathematicalContingency.CohenConditions

/-! Unconditional finite-condition size bound at the second Hartogs stage,
relative to the paper's displayed Peano and RC assumptions.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

theorem conditionBit_embeds_two (A : α → Prop) (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b) :
    Embeds ConditionBit A := by
  refine ⟨fun p x => (p = True ∧ x = a) ∨ (p = False ∧ x = b),⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro p x h
    exact h.elim (fun h => ⟨Or.inl h.1,h.2 ▸ ha⟩) (fun h => ⟨Or.inr h.1,h.2 ▸ hb⟩)
  · intro p hp
    exact hp.elim (fun h => ⟨a,ha,Or.inl ⟨h,rfl⟩⟩) (fun h => ⟨b,hb,Or.inr ⟨h,rfl⟩⟩)
  · intro p x y hx hy
    obtain hx | hx := hx
    · obtain hy | hy := hy
      · exact hx.2.trans hy.2.symm
      · exact (conditionBit_distinct (hx.1.symm.trans hy.1)).elim
    · obtain hy | hy := hy
      · exact (conditionBit_distinct (hy.1.symm.trans hx.1)).elim
      · exact hx.2.trans hy.2.symm
  · intro p q x hp hq
    obtain hp | hp := hp
    · obtain hq | hq := hq
      · exact hp.1.trans hq.1.symm
      · exact (hne (hp.2.symm.trans hq.2)).elim
    · obtain hq | hq := hq
      · exact (hne (hq.2.symm.trans hp.2)).elim
      · exact hp.1.trans hq.1.symm

theorem doubleHartogs_pairing (A : α → Prop) (L : α → α → Prop) (hw : WellOrderOn A L)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b)
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → OrdinalCarrier (OrdinalCarrier α) → Prop)) :
    ∃ R, PairingOn (HartogsCarrier (HartogsCarrier A)) R := by
  obtain ⟨R,hR⟩ := hartogs_pairing A rc1 rp1 Q hq a b ha hb hne
  obtain ⟨u,v,hu,hv,huv⟩ := embeds_preserves_two A _ (wellOrder_embeds_hartogs rc1 A L hw) a b ha hb hne
  exact hartogs_pairing (HartogsCarrier A) rc2 rp2 R hR u v hu hv huv

theorem doubleHartogs_cardinal_bounds (A : α → Prop) (L : α → α → Prop) (hw : WellOrderOn A L)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b)
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → OrdinalCarrier (OrdinalCarrier α) → Prop)) :
    Embeds (RigidFinitePower (HartogsCarrier (HartogsCarrier A))) (HartogsCarrier (HartogsCarrier A)) ∧
    Embeds (FiniteCondition A (HartogsCarrier (HartogsCarrier A)) ConditionBit) (HartogsCarrier (HartogsCarrier A)) := by
  let H := HartogsCarrier A
  let J := HartogsCarrier H
  have wH := hartogs_wellOrder rc1 A
  have wJ := hartogs_wellOrder rc2 H
  have emb : Embeds A J := embeds_trans A H J (wellOrder_embeds_hartogs rc1 A L hw)
    (wellOrder_embeds_hartogs rc2 H (HartogsOrder A) wH)
  obtain ⟨u,v,hu,hv,huv⟩ := embeds_preserves_two A J emb a b ha hb hne
  obtain ⟨R,hR⟩ := doubleHartogs_pairing A L hw Q hq a b ha hb hne rc1 rp1 rc2 rp2
  exact ⟨finitePower_absorption_of_pairing J (HartogsOrder H) R wJ hR u v hu hv huv,
    finiteCondition_bound_of_pairing A J ConditionBit J R rc2 (HartogsOrder H) wJ hR u v hu hv huv
      emb (embeds_refl J) (conditionBit_embeds_two J u v hu hv huv)⟩

theorem natural_secondHartogs_cardinal_bounds {σ : Type} [Ty σ] (hp : LowerPeano σ)
    (rc1 : P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((σ → Prop) → Prop)) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((σ → Prop) → Prop)) →
      OrdinalCarrier (OrdinalCarrier ((σ → Prop) → Prop)) → Prop)) :
    Embeds (RigidFinitePower (HartogsCarrier (HartogsCarrier (@LowerNat σ _)))) (HartogsCarrier (HartogsCarrier (@LowerNat σ _))) ∧
    Embeds (@CohenCondition σ _ _ _ (HartogsCarrier (HartogsCarrier (@LowerNat σ _))))
      (HartogsCarrier (HartogsCarrier (@LowerNat σ _))) :=
  doubleHartogs_cardinal_bounds LowerNat LowerLT (lowerNat_wellOrder hp) LowerPair (lowerPair_pairing hp)
    (AtLeastZero σ) (SucCard (AtLeastZero σ)) lowerNat_zero (lowerNat_suc _ lowerNat_zero)
    (lowerNat_ne_suc_self hp _ lowerNat_zero) rc1 rp1 rc2 rp2

#classicism_check conditionBit_embeds_two doubleHartogs_pairing doubleHartogs_cardinal_bounds natural_secondHartogs_cardinal_bounds
#classicism_types conditionBit_embeds_two doubleHartogs_pairing doubleHartogs_cardinal_bounds natural_secondHartogs_cardinal_bounds
end Classicism.MathematicalContingency
