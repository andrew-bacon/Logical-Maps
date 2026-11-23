import Classicism.Results.MathematicalContingency.PairOrder

/-! Well-ordering pairs and bounding their predecessor segments.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem maxPairOrder_wellOrder (A : α → Prop) (L : α → α → Prop) (hw : WellOrderOn A L) :
    WellOrderOn (PairCarrier A) (MaxPairOrder A L) := by
  refine ⟨maxPairOrder_strict A L hw.1,?_⟩
  intro X hX he
  obtain ⟨P0,hP0⟩ := he
  obtain ⟨m0,x0,y0,h0⟩ := pairMaxAt_exists A L hw.1 P0 (hX P0 hP0)
  let M := fun m => ∃ P x y, X P ∧ PairMaxAt A L P m x y
  obtain ⟨m,hm,hmin⟩ := hw.2 M
    (fun m h => h.elim fun P h => h.elim fun x h => h.elim fun y h => pairMaxAt_member A L P m x y h.2)
    ⟨m0,P0,x0,y0,hP0,h0⟩
  obtain ⟨P1,x1,y1,hP1,h1⟩ := hm
  let U := fun x => ∃ P y, X P ∧ PairMaxAt A L P m x y
  obtain ⟨x,hx,hxmin⟩ := hw.2 U
    (fun x h => h.elim fun P h => h.elim fun y h => h.2.1.1) ⟨x1,P1,y1,hP1,h1⟩
  obtain ⟨P2,y2,hP2,h2⟩ := hx
  let V := fun y => ∃ P, X P ∧ PairMaxAt A L P m x y
  obtain ⟨y,hy,hymin⟩ := hw.2 V
    (fun y h => h.elim fun P h => h.2.1.2.1) ⟨y2,P2,hP2,h2⟩
  obtain ⟨P,hP,h⟩ := hy
  refine ⟨P,hP,?_⟩
  intro Q hQ hQP
  obtain ⟨n,u,v,k⟩ := pairMaxAt_exists A L hw.1 Q (hX Q hQ)
  obtain hlt | ⟨en,hlt⟩ := (maxPairOrder_at A L hw.1 Q P n u v m x y k h).mp hQP
  · exact hmin n ⟨Q,u,v,hQ,k⟩ hlt
  · subst n
    obtain hlt | ⟨eu,hlt⟩ := hlt
    · exact hxmin u ⟨Q,v,hQ,k⟩ hlt
    · subst u
      exact hymin v ⟨Q,hQ,k⟩ hlt

def ClosedSegment (A : α → Prop) (L : α → α → Prop) (m : α) : α → Prop :=
  fun x => A x ∧ OrderLe L x m

theorem maxPairOrder_segment_coordinates (A : α → Prop) (L : α → α → Prop)
    (hs : StrictOrderOn A L) (P Q : α → α → Prop) (m u v : α)
    (hQ : PairMaxAt A L Q m u v) (h : MaxPairOrder A L P Q) :
    PairCarrier (ClosedSegment A L m) P := by
  obtain ⟨n,x,y,hP⟩ := pairMaxAt_exists A L hs P ((maxPairOrder_strict A L hs).1 P Q h).1
  have hnm : OrderLe L n m := ((maxPairOrder_at A L hs P Q n x y m u v hP hQ).mp h).elim
    Or.inr (fun h => Or.inl h.1)
  have hn := pairMaxAt_member A L P n x y hP
  have hm := pairMaxAt_member A L Q m u v hQ
  exact ⟨x,y,⟨hP.1.1,orderLe_trans A L hs x n m hP.1.1 hn hm hP.2.2.1 hnm⟩,
    ⟨hP.1.2.1,orderLe_trans A L hs y n m hP.1.2.1 hn hm hP.2.2.2 hnm⟩,hP.1.2.2⟩

theorem maxPairOrder_segments_embed (A : α → Prop) (L : α → α → Prop)
    (hs : StrictOrderOn A L) (B : β → Prop) (Q : β → β → β → Prop) (hq : PairingOn B Q)
    (bounds : ∀ m, A m → Embeds (ClosedSegment A L m) B) :
    ∀ P, PairCarrier A P → Embeds (Segment (PairCarrier A) (MaxPairOrder A L) P) B := by
  intro P hp
  obtain ⟨m,x,y,hm⟩ := pairMaxAt_exists A L hs P hp
  obtain ⟨F,hF⟩ := bounds m (pairMaxAt_member A L P m x y hm)
  exact embeds_trans _ (PairCarrier (ClosedSegment A L m)) B
    (embeds_of_subset _ _ (fun R h => maxPairOrder_segment_coordinates A L hs R P m x y hm h.2))
    (pairCarrier_embeds_from_coordinates (ClosedSegment A L m) B F Q hF hq)

#classicism_check maxPairOrder_wellOrder maxPairOrder_segment_coordinates maxPairOrder_segments_embed
#classicism_types maxPairOrder_wellOrder maxPairOrder_segment_coordinates maxPairOrder_segments_embed
end Classicism.MathematicalContingency
