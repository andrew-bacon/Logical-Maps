import Classicism.Results.MathematicalContingency.PairWellOrder

/-! A pairing relation lifts to the next Hartogs cardinal.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem embeds_adjoin_of_pairing (X : α → Prop) (p : α) (B : β → Prop)
    (Q : β → β → β → Prop) (hq : PairingOn B Q) (a b : β) (ha : B a) (hb : B b) (hne : a ≠ b)
    (emb : Embeds X B) : Embeds (fun x => X x ∨ x = p) B := by
  obtain hp | hp := em (X p)
  · exact embeds_trans _ X B (embeds_of_subset _ _ (fun x h => h.elim id (fun e => e ▸ hp))) emb
  · obtain ⟨F,hF⟩ := emb
    refine ⟨fun x z => (∃ u, F x u ∧ Q a u z) ∨ (x = p ∧ Q b a z),⟨⟨?_,?_,?_⟩,?_⟩⟩
    · intro x z h
      exact h.elim (fun ⟨u,hxu,hz⟩ => ⟨Or.inl (hF.1.1 x u hxu).1,(hq.1 a u z hz).2.2⟩)
        (fun h => ⟨Or.inr h.1,(hq.1 b a z h.2).2.2⟩)
    · intro x hx
      obtain hx | e := hx
      · obtain ⟨u,hu,hxu⟩ := hF.1.2.1 x hx
        obtain ⟨z,hz,hqz⟩ := hq.2.1 a u ha hu
        exact ⟨z,hz,Or.inl ⟨u,hxu,hqz⟩⟩
      · obtain ⟨z,hz,hqz⟩ := hq.2.1 b a hb ha
        exact ⟨z,hz,Or.inr ⟨e,hqz⟩⟩
    · intro x z w hz hw
      obtain ⟨u,hxu,hz⟩ | ⟨e,hz⟩ := hz
      · obtain ⟨v,hxv,hw⟩ | ⟨e,_⟩ := hw
        · have ev := hF.1.2.2 x u v hxu hxv
          subst v
          exact hq.2.2.1 a u z w hz hw
        · exact (hp (e ▸ (hF.1.1 x u hxu).1)).elim
      · obtain ⟨v,hxv,_⟩ | ⟨_,hw⟩ := hw
        · exact (hp (e ▸ (hF.1.1 x v hxv).1)).elim
        · exact hq.2.2.1 b a z w hz hw
    · intro x y z hx hy
      obtain ⟨u,hxu,hz⟩ | ⟨ex,hz⟩ := hx
      · obtain ⟨v,hyv,hw⟩ | ⟨_,hw⟩ := hy
        · have ev := (hq.2.2.2 a u a v z hz hw).2
          subst v
          exact hF.2 x y u hxu hyv
        · exact (hne (hq.2.2.2 a u b a z hz hw).1).elim
      · obtain ⟨v,_,hw⟩ | ⟨ey,_⟩ := hy
        · exact (hne (hq.2.2.2 a v b a z hw hz).1).elim
        · exact ex.trans ey.symm

theorem hartogs_closedSegment_embeds (A : α → Prop) (Q : α → α → α → Prop)
    (hq : PairingOn A Q) (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b)
    (m : OrdinalCarrier α) (hm : HartogsCarrier A m) :
    Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) m) A :=
  embeds_trans _ (fun x => Segment (HartogsCarrier A) (HartogsOrder A) m x ∨ x = m) A
    (embeds_of_subset _ _ (fun x h => h.2.elim Or.inr (fun hlt => Or.inl ⟨h.1,hlt⟩)))
    (embeds_adjoin_of_pairing _ m A Q hq a b ha hb hne (hartogs_segment_embeds A m hm))

theorem hartogs_pairCarrier_embeds (A : α → Prop)
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b) :
    Embeds (PairCarrier (HartogsCarrier A)) (HartogsCarrier A) :=
  wellOrder_embeds_hartogs_of_segments rc A _ _
    (maxPairOrder_wellOrder _ _ (hartogs_wellOrder rc A))
    (maxPairOrder_segments_embed _ _ (hartogs_wellOrder rc A).1 A Q hq
      (hartogs_closedSegment_embeds A Q hq a b ha hb hne))

theorem hartogs_pairing (A : α → Prop)
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rcPair : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b) :
    ∃ R, PairingOn (HartogsCarrier A) R :=
  pairing_of_pairCarrier_embedding _ rcPair (hartogs_pairCarrier_embeds A rc Q hq a b ha hb hne)

theorem embeds_preserves_two (A : α → Prop) (B : β → Prop) (emb : Embeds A B)
    (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b) : ∃ u v, B u ∧ B v ∧ u ≠ v := by
  obtain ⟨F,hF⟩ := emb
  obtain ⟨u,hu,hau⟩ := hF.1.2.1 a ha
  obtain ⟨v,hv,hbv⟩ := hF.1.2.1 b hb
  exact ⟨u,v,hu,hv,fun e => hne (hF.2 a b u hau (e.symm ▸ hbv))⟩

#classicism_check embeds_adjoin_of_pairing hartogs_closedSegment_embeds hartogs_pairCarrier_embeds hartogs_pairing embeds_preserves_two
#classicism_types embeds_adjoin_of_pairing hartogs_closedSegment_embeds hartogs_pairCarrier_embeds hartogs_pairing embeds_preserves_two
end Classicism.MathematicalContingency
