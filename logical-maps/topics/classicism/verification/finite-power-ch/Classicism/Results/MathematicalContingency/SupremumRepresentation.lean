import Classicism.Results.MathematicalContingency.DecisionRepresentation

/-!
Relational supremum values and their interval representation.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
No choice of a supremum function or infinite distributivity is needed.
-/
namespace Classicism.MathematicalContingency
variable {β : Type} [Ty β]

def RepresentedSupremum (B : β → Prop) (R : β → β → Prop)
    (X : β → Prop) (F : β → Prop → Prop) (p : Prop) : Prop :=
  ∃ b, Supremum B R X b ∧ F b p

theorem supremum_unique (B : β → Prop) (R : β → β → Prop)
    (order : PartialOrderOn B R) (X : β → Prop) (b c : β)
    (hb : Supremum B R X b) (hc : Supremum B R X c) : b = c :=
  order.2.2.1 b c (hb.2.2 c hc.1 hc.2.1) (hc.2.2 b hb.1 hb.2.1)

theorem representedSupremum_exists (B : β → Prop) (R : β → β → Prop)
    (complete : ∀ X : β → Prop, (∀ x, X x → B x) → ∃ b, Supremum B R X b)
    (F : β → Prop → Prop) (P : Prop) (maps : Maps F B (Below P))
    (X : β → Prop) (sub : ∀ x, X x → B x) :
    ∃ p, RepresentedSupremum B R X F p := by
  obtain ⟨b,hb⟩ := complete X sub
  obtain ⟨p,_,hp⟩ := maps.2.1 b hb.1
  exact ⟨p,b,hb,hp⟩

theorem representedSupremum_functional (B : β → Prop) (R : β → β → Prop)
    (order : PartialOrderOn B R) (F : β → Prop → Prop) (P : Prop)
    (maps : Maps F B (Below P)) (X : β → Prop) (p q : Prop)
    (hp : RepresentedSupremum B R X F p)
    (hq : RepresentedSupremum B R X F q) : p = q := by
  obtain ⟨b,hb,hbp⟩ := hp
  obtain ⟨c,hc,hcq⟩ := hq
  have e := supremum_unique B R order X b c hb hc
  exact maps.2.2 c p q (e ▸ hbp) hcq

theorem representedSupremum_above (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder)
    (X : β → Prop) (p : Prop) (hp : RepresentedSupremum B R X F p)
    (b : β) (q : Prop) (hb : X b) (hq : F b q) : EntailmentOrder q p := by
  obtain ⟨s,hs,hsp⟩ := hp
  exact (iso.2 b s q p hq hsp).mp (hs.2.1 b hb)

theorem representedSupremum_below (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder)
    (X : β → Prop) (sub : ∀ x, X x → B x)
    (p : Prop) (hp : RepresentedSupremum B R X F p)
    (q : Prop) (below : Below P q)
    (upper : ∀ b r, X b → F b r → EntailmentOrder r q) : EntailmentOrder p q := by
  obtain ⟨s,hs,hsp⟩ := hp
  obtain ⟨c,hc,hcq⟩ := iso.1.2.2 q below
  have bound : R s c := hs.2.2 c hc (by
    intro b hb
    obtain ⟨r,_,hbr⟩ := iso.1.1.1.2.1 b (sub b hb)
    exact (iso.2 b c r q hbr hcq).mpr (upper b r hb hbr))
  exact (iso.2 s c p q hsp hcq).mp bound

/-- Pull back P and not q as an upper bound for the generators. This avoids
an infinitary Boolean-algebra lemma and uses only the displayed supremum. -/
theorem representedSupremum_disjoint (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (o : β) (zero : F o False)
    (X : β → Prop) (sub : ∀ x, X x → B x)
    (p : Prop) (hp : RepresentedSupremum B R X F p)
    (c : β) (q : Prop) (hc : F c q)
    (disjoint : ∀ b, X b → Meets B R c b o) : EntailmentOrder q (¬ p) := by
  have bound : EntailmentOrder p (P ∧ ¬ q) := representedSupremum_below B R F P iso
    X sub p hp (P ∧ ¬ q) (nec% (fun h : P ∧ ¬ q => h.1)) (by
      intro b r hb hbr
      have hn := intervalIso_meet_zero B R F P iso o c b q r zero hc hbr (disjoint b hb)
      exact modal_K _ _ (modal_K _ _
        (nec% (fun (h : r → P) (k : r → ¬ q) (hr : r) => And.intro (h hr) (k hr)))
        (iso.1.1.1.1 b r hbr).2) hn)
  exact modal_K _ _
    (nec% (fun (h : p → P ∧ ¬ q) (hq : q) (hp : p) => (h hp).2 hq)) bound

#classicism_check supremum_unique representedSupremum_exists representedSupremum_functional
  representedSupremum_above representedSupremum_below representedSupremum_disjoint
#classicism_types supremum_unique representedSupremum_exists representedSupremum_functional
  representedSupremum_above representedSupremum_below representedSupremum_disjoint
end Classicism.MathematicalContingency
