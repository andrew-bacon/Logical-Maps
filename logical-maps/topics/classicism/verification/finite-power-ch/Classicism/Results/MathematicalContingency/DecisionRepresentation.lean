import Classicism.Results.MathematicalContingency.BooleanDecisions
import Classicism.Results.MathematicalContingency.DensityEntailment
namespace Classicism.MathematicalContingency
variable {σ β : Type} [Ty σ] [Ty β]

def LocalDecisions (A : σ → Prop) (P : Prop) : Prop :=
  ∀ X : σ → Prop, ∀ Q, Q ≠ False → EntailmentOrder Q P →
    ∃ q, q ≠ False ∧ EntailmentOrder q Q ∧
      ∀ a, A a → EntailmentOrder q (X a) ∨ EntailmentOrder q (¬ X a)

theorem entailment_trans (p q r : Prop) (h : EntailmentOrder p q)
    (k : EntailmentOrder q r) : EntailmentOrder p r :=
  modal_K _ _ (modal_K _ _ (nec% (fun (h : p → q) (k : q → r) (hp : p) => k (h hp))) h) k

theorem intervalIso_order_forward (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (hf : OrderIso F B R (Below P) EntailmentOrder)
    (a b : β) (p q : Prop) (ha : F a p) (hb : F b q) (h : R a b) : EntailmentOrder p q :=
  (hf.2 a b p q ha hb).mp h

theorem intervalIso_order_backward (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (hf : OrderIso F B R (Below P) EntailmentOrder)
    (a b : β) (p q : Prop) (ha : F a p) (hb : F b q) (h : EntailmentOrder p q) : R a b :=
  (hf.2 a b p q ha hb).mpr h

theorem intervalIso_meet_zero (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (hf : OrderIso F B R (Below P) EntailmentOrder)
    (o x y : β) (p q : Prop) (ho : F o False) (hx : F x p) (hy : F y q)
    (hm : Meets B R x y o) : EntailmentOrder q (¬ p) := by
  have hsub : Below P (p ∧ q) := entailment_trans (p ∧ q) p P
    (nec% (fun h : p ∧ q => h.1)) (hf.1.1.1.1 x p hx).2
  obtain ⟨v,hv,hvF⟩ := hf.1.2.2 (p ∧ q) hsub
  have hvo : R v o := hm.2.2 v hv (by
    intro u hu
    exact hu.elim
      (fun e => e.symm ▸ intervalIso_order_backward B R F P hf v x (p ∧ q) p hvF hx (nec% (fun h : p ∧ q => h.1)))
      (fun e => e.symm ▸ intervalIso_order_backward B R F P hf v y (p ∧ q) q hvF hy (nec% (fun h : p ∧ q => h.2))))
  obtain ⟨z,_,hoz⟩ := hf.1.1.1.2.1 o hm.1
  have hz : z = False := hf.1.1.1.2.2 o z False hoz ho
  have hto := intervalIso_order_forward B R F P hf v o (p ∧ q) z hvF hoz hvo
  exact modal_K _ _ (modal_K _ _
    (nec% (fun (h : p ∧ q → z) (hn : ¬ z) (hq : q) (hp : p) => hn (h ⟨hp,hq⟩))) hto)
    ((box_not_eq z).mpr hz)

theorem intervalIso_decision (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (hf : OrderIso F B R (Below P) EntailmentOrder)
    (o i c b : β) (q p : Prop) (ho : F o False) (hc : F c q) (hb : F b p)
    (hd : DecidesAt B R o i c b) : EntailmentOrder q p ∨ EntailmentOrder q (¬ p) := by
  obtain h | ⟨d,hd,hcd⟩ := hd
  · exact Or.inl ((hf.2 c b q p hc hb).mp h)
  · obtain ⟨r,_,hr⟩ := hf.1.1.1.2.1 d hd.1
    exact Or.inr (entailment_trans q r (¬ p) ((hf.2 c d q r hc hr).mp hcd)
      (intervalIso_meet_zero B R F P hf o b d p r ho hb hr hd.2.1))

theorem intervalIso_sequence (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (hf : OrderIso F B R (Below P) EntailmentOrder)
    (X : ((σ → Prop) → Prop) → Prop) :
    Maps (fun n b => LowerNat n ∧ F b (P ∧ X n)) LowerNat B := by
  refine ⟨fun n b h => ⟨h.1,(hf.1.1.1.1 b _ h.2).1⟩,?_,?_⟩
  · intro n hn
    obtain ⟨b,hb,hF⟩ := hf.1.2.2 (P ∧ X n) (nec% (fun h : P ∧ X n => h.1))
    exact ⟨b,hb,hn,hF⟩
  · intro n b c hb hc
    exact hf.1.1.2 b c (P ∧ X n) hb.2 hc.2

theorem binaryDecisions_local (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (o i : β)
    (hf : OrderIso F B R (Below P) EntailmentOrder) (ho : F o False)
    (hd : @BinaryDecisionProperty σ β _ _ B R o i) : LocalDecisions (@LowerNat σ _) P := by
  intro X Q hnQ hQP
  obtain ⟨b,hb,hbQ⟩ := hf.1.2.2 Q hQP
  have hbn : b ≠ o := fun e => hnQ ((intervalIso_zero_iff B R F P hf o b Q ho hbQ).mp e)
  obtain ⟨c,hc,hcn,hcb,hdec⟩ := hd (fun n b => LowerNat n ∧ F b (P ∧ X n))
    (intervalIso_sequence B R F P hf X) b hb hbn
  obtain ⟨q,hqP,hcq⟩ := hf.1.1.1.2.1 c hc
  refine ⟨q,(fun e => hcn ((intervalIso_zero_iff B R F P hf o c q ho hcq).mpr e)),
    (hf.2 c b q Q hcq hbQ).mp hcb,?_⟩
  intro n hn
  obtain ⟨x,_,hx⟩ := (intervalIso_sequence B R F P hf X).2.1 n hn
  obtain hp | hm := intervalIso_decision B R F P hf o i c x q (P ∧ X n) ho hcq hx.2
    (hdec n x hn hx)
  · exact Or.inl (entailment_trans q (P ∧ X n) (X n) hp (nec% (fun h : P ∧ X n => h.2)))
  · exact Or.inr (modal_K _ _ (modal_K _ _
      (nec% (fun (h : q → P) (k : q → ¬ (P ∧ X n)) (hq : q) (hx : X n) => k hq ⟨h hq,hx⟩)) hqP) hm)

#classicism_check intervalIso_order_forward intervalIso_order_backward entailment_trans intervalIso_meet_zero intervalIso_decision intervalIso_sequence binaryDecisions_local
#classicism_types intervalIso_order_forward intervalIso_order_backward entailment_trans intervalIso_meet_zero intervalIso_decision intervalIso_sequence binaryDecisions_local
end Classicism.MathematicalContingency
