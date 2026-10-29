import Classicism.Results.MathematicalContingency.BooleanDecisions
import Classicism.Results.MathematicalContingency.RigidImageCoding

/-!
A Boolean algebra is separated by the basic cones below its elements.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
This derives its rigid-power cardinal bound from CBA and DenseCones, before
MP is applied. No interval representation or incompatibility preservation is
used in this cardinal argument; those remain distinct forcing requirements.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

theorem complementAt_symm (B : β → Prop) (R : β → β → Prop) (o i x y : β)
    (hx : B x) (h : ComplementAt B R o i x y) : ComplementAt B R o i y x := by
  refine ⟨hx,⟨h.2.1.1,?_,?_⟩,⟨h.2.2.1,?_,?_⟩⟩
  · intro u hu
    exact h.2.1.2.1 u (hu.elim Or.inr Or.inl)
  · intro v hv lower
    exact h.2.1.2.2 v hv (fun u hu => lower u (hu.elim Or.inr Or.inl))
  · intro u hu
    exact h.2.2.2.1 u (hu.elim Or.inr Or.inl)
  · intro v hv upper
    exact h.2.2.2.2 v hv (fun u hu => upper u (hu.elim Or.inr Or.inl))

theorem cba_endpoints_at_bottom (B : β → Prop) (R : β → β → Prop) (cba : CBA B R)
    (o : β) (member : B o) (least : ∀ b, B b → R o b) :
    ∃ i, Endpoints B R o i ∧ ∀ b, B b → ∃ d, ComplementAt B R o i b d := by
  obtain ⟨z,i,endpoints,complements⟩ := cba.2.2.2.2
  have e : z = o := cba.1.2.2.1 z o (endpoints.2.2 o member).1 (least z endpoints.1)
  subst z
  exact ⟨i,endpoints,complements⟩

/-- Boolean order is reflected by inclusion of the basic cones lying below
each element. This is not reflection of the original condition order. -/
theorem denseCones_order_reflect (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o i : β) (C : α → β → Prop)
    (cba : CBA B R) (endpoints : Endpoints B R o i)
    (complements : ∀ b, B b → ∃ d, ComplementAt B R o i b d)
    (cones : DenseCones Q E B R o C) (b c : β) (hb : B b) (hc : B c)
    (below : ∀ q x, C q x → R x b → R x c) : R b c := by
  obtain ⟨d,hd⟩ := complements c hc
  obtain ⟨v,hv⟩ := cba_meet_exists B R cba b d hb hd.1
  have zero : v = o := by
    obtain eq | ne := em (v = o)
    · exact eq
    · obtain ⟨q,x,_,hqx,hxv⟩ := cones.2.2.2.1 v hv.1 ne
      have hx : B x := (cones.1.1 q x hqx).2
      have hxb : R x b := cba.1.2.2.2 x v b hxv (hv.2.1 b (Or.inl rfl))
      have hxc : R x c := below q x hqx hxb
      have hxd : R x d := cba.1.2.2.2 x v d hxv (hv.2.1 d (Or.inr rfl))
      have hxo : R x o := hd.2.1.2.2 x hx (by
        intro u hu
        exact hu.elim (fun e => e.symm ▸ hxc) (fun e => e.symm ▸ hxd))
      exact (cones.2.1 q x hqx (cba.1.2.2.1 x o hxo (endpoints.2.2 x hx).1)).elim
  exact cba_disjoint_complement B R cba o i b d c endpoints hb hd.1
    (complementAt_symm B R o i c d hc hd) (zero ▸ hv)

def ConeTrace (C : α → β → Prop) (R : β → β → Prop) (b : β) (q : α) : Prop :=
  ∃ c, C q c ∧ R c b

theorem coneTrace_sub (Q : α → Prop) (B : β → Prop) (C : α → β → Prop)
    (R : β → β → Prop) (maps : Maps C Q B) (b : β) :
    ∀ q, ConeTrace C R b q → Q q := by
  intro q h
  obtain ⟨c,hqc,_⟩ := h
  exact (maps.1 q c hqc).1

theorem coneTrace_separates (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop)
    (cba : CBA B R) (member : B o) (least : ∀ b, B b → R o b)
    (cones : DenseCones Q E B R o C) (b c : β) (hb : B b) (hc : B c)
    (coext : ConeTrace C R b ≡ ConeTrace C R c) : b = c := by
  obtain ⟨i,endpoints,complements⟩ := cba_endpoints_at_bottom B R cba o member least
  apply cba.1.2.2.1 b c
  · apply denseCones_order_reflect Q E B R o i C cba endpoints complements cones b c hb hc
    intro q x hqx hxb
    obtain ⟨y,hqy,hyc⟩ := (coext q).mp ⟨x,hqx,hxb⟩
    exact (cones.1.2.2 q y x hqy hqx) ▸ hyc
  · apply denseCones_order_reflect Q E B R o i C cba endpoints complements cones c b hc hb
    intro q x hqx hxc
    obtain ⟨y,hqy,hyb⟩ := (coext q).mpr ⟨x,hqx,hxc⟩
    exact (cones.1.2.2 q y x hqy hqx) ▸ hyb

/-- Push the traces into J before taking rigid representatives. This requires
RC only at J's predicate type, not at the condition-predicate type. -/
theorem denseCones_embeds_rigidPower (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop)
    (cba : CBA B R) (member : B o) (least : ∀ b, B b → R o b)
    (cones : DenseCones Q E B R o C) (J : γ → Prop)
    (rc : P.RigidComprehension (γ → Prop)) (bound : Embeds Q J) :
    Embeds B (RigidPower J) :=
  rigidImageCode_embeds Q J B (ConeTrace C R) rc bound
    (fun b _ => coneTrace_sub Q B C R cones.1 b)
    (coneTrace_separates Q E B R o C cba member least cones)

#classicism_check complementAt_symm cba_endpoints_at_bottom denseCones_order_reflect
  coneTrace_sub coneTrace_separates denseCones_embeds_rigidPower
#classicism_types complementAt_symm cba_endpoints_at_bottom denseCones_order_reflect
  coneTrace_sub coneTrace_separates denseCones_embeds_rigidPower
end Classicism.MathematicalContingency
