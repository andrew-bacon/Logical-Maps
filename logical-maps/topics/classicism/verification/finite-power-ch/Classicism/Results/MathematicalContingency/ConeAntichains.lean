import Classicism.Results.MathematicalContingency.CohenSeparation
import Classicism.Results.MathematicalContingency.CarrierTheory
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem denseCones_representation (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop)
    (F : β → Prop → Prop) (P : Prop) (hc : DenseCones Q E B R o C)
    (hf : OrderIso F B R (Below P) EntailmentOrder) (ho : F o False) :
    PropositionCones Q E (RelCompose C F) P := by
  refine ⟨maps_compose C F Q B (Below P) hc.1 hf.1.1.1,?_,?_,?_⟩
  · intro q p h
    obtain ⟨b,hqb,hbp⟩ := h
    exact fun e => hc.2.1 q b hqb ((intervalIso_zero_iff B R F P hf o b p ho hbp).mpr e)
  · intro q r p s hq hr he
    obtain ⟨b,hqb,hbp⟩ := hq
    obtain ⟨c,hrc,hcs⟩ := hr
    exact intervalIso_order_forward B R F P hf c b s p hcs hbp (hc.2.2.1 q r b c hqb hrc he)
  · intro p hn hp
    obtain ⟨b,hb,hbp⟩ := hf.1.2.2 p hp
    have hbn : b ≠ o := fun e => hn ((intervalIso_zero_iff B R F P hf o b p ho hbp).mp e)
    obtain ⟨q,c,hq,hqc,hcb⟩ := hc.2.2.2.1 b hb hbn
    obtain ⟨s,_,hcs⟩ := hf.1.1.1.2.1 c (hc.1.1 q c hqc).2
    exact ⟨q,s,hq,⟨c,hqc,hcs⟩,intervalIso_order_forward B R F P hf c b s p hcs hbp hcb⟩

def NonzeroAntichain (B : β → Prop) (R : β → β → Prop) (o : β) (U : β → Prop) : Prop :=
  (∀ b, U b → B b ∧ b ≠ o) ∧
  ∀ b c v, U b → U c → b ≠ c → B v → R v b → R v c → v = o

def LeastCone (Q : α → Prop) (L : α → α → Prop) (R : β → β → Prop)
    (C : α → β → Prop) (U : β → Prop) (b : β) (q : α) : Prop :=
  LeastRelated U Q L (fun b q => ∃ v, C q v ∧ R v b) b q

def SelectedCones (Q : α → Prop) (L : α → α → Prop) (R : β → β → Prop)
    (C : α → β → Prop) (U : β → Prop) (q : α) : Prop := ∃ b, LeastCone Q L R C U b q

theorem leastCone_total (Q : α → Prop) (E L : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop) (U : β → Prop)
    (hw : WellOrderOn Q L) (hc : DenseCones Q E B R o C) (hu : NonzeroAntichain B R o U)
    (b : β) (hb : U b) : ∃ q, LeastCone Q L R C U b q := by
  apply leastRelated_exists U Q L (fun b q => ∃ v, C q v ∧ R v b) hw ?_ b hb
  intro b hb
  obtain ⟨q,v,hq,hqv,hvb⟩ := hc.2.2.2.1 b (hu.1 b hb).1 (hu.1 b hb).2
  exact ⟨q,hq,v,hqv,hvb⟩

theorem leastCone_common_extension (Q : α → Prop) (E L : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop) (U : β → Prop)
    (hp : PartialOrderOn B R) (hc : DenseCones Q E B R o C) (hu : NonzeroAntichain B R o U)
    (b c : β) (q r s : α) (hb : LeastCone Q L R C U b q) (hd : LeastCone Q L R C U c r)
    (hs : Q s) (hsq : E s q) (hsr : E s r) : b = c := by
  obtain ⟨v,hqv,hvb⟩ := hb.2.2.1
  obtain ⟨w,hrw,hwc⟩ := hd.2.2.1
  obtain ⟨z,hz,hsz⟩ := hc.1.2.1 s hs
  apply (em (b = c)).elim id
  intro hn
  exact (hc.2.1 s z hsz (hu.2 b c z hb.1 hd.1 hn hz
    (hp.2.2.2 z v b (hc.2.2.1 q s v z hqv hsz hsq) hvb)
    (hp.2.2.2 z w c (hc.2.2.1 r s w z hrw hsz hsr) hwc))).elim

theorem leastCone_bijects (Q : α → Prop) (E L : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop) (U : β → Prop)
    (hq : PartialOrderOn Q E) (hp : PartialOrderOn B R) (hw : WellOrderOn Q L)
    (hc : DenseCones Q E B R o C) (hu : NonzeroAntichain B R o U) :
    Bijects (LeastCone Q L R C U) U (SelectedCones Q L R C U) := by
  have hm : Maps (LeastCone Q L R C U) U (SelectedCones Q L R C U) :=
    ⟨fun b q h => ⟨h.1,b,h⟩,
      fun b hb => (leastCone_total Q E L B R o C U hw hc hu b hb).elim (fun q h => ⟨q,⟨b,h⟩,h⟩),
      fun b q r hb hc => leastRelated_unique U Q L (fun b q => ∃ v, C q v ∧ R v b) hw b q r hb hc⟩
  refine ⟨⟨hm,?_⟩,hm,?_⟩
  · intro b c q hb hc'
    exact leastCone_common_extension Q E L B R o C U hp hc hu b c q q q hb hc' hb.2.1
      (hq.2.1 q hb.2.1) (hq.2.1 q hb.2.1)
  · intro q hq
    obtain ⟨b,hb⟩ := hq
    exact ⟨b,hb.1,hb⟩

theorem selectedCones_incompatible (Q : α → Prop) (E L : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop) (U : β → Prop)
    (hp : PartialOrderOn B R) (hw : WellOrderOn Q L)
    (hc : DenseCones Q E B R o C) (hu : NonzeroAntichain B R o U)
    (q r : α) (hq : SelectedCones Q L R C U q) (hr : SelectedCones Q L R C U r) (hne : q ≠ r) :
    ¬ ∃ s, Q s ∧ E s q ∧ E s r := by
  obtain ⟨b,hb⟩ := hq
  obtain ⟨c,hd⟩ := hr
  intro ⟨s,hs,hsq,hsr⟩
  have e := leastCone_common_extension Q E L B R o C U hp hc hu b c q r s hb hd hs hsq hsr
  have hd' : LeastCone Q L R C U b r := e.symm ▸ hd
  exact hne (leastRelated_unique U Q L (fun b q => ∃ v, C q v ∧ R v b) hw b q r hb hd')

#classicism_check denseCones_representation leastCone_total leastCone_common_extension leastCone_bijects selectedCones_incompatible
#classicism_types denseCones_representation leastCone_total leastCone_common_extension leastCone_bijects selectedCones_incompatible
end Classicism.MathematicalContingency
