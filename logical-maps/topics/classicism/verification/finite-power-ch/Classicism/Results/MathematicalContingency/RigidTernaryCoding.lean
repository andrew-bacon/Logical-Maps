import Classicism.Results.MathematicalContingency.PairingAbsorption
import Classicism.Results.MathematicalContingency.RigidImageCoding

namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

def RigidTernaryPower (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (R : α → β → γ → Prop) : Prop :=
  Rigid R ∧ ∀ x y z, R x y z → A x ∧ B y ∧ D z

theorem ternaryImage_typed_reflect (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (E : α → β → γ → δ → Prop)
    (total : ∀ x y z, A x → B y → D z → ∃ d, J d ∧ E x y z d)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w)
    (R S : α → β → γ → Prop)
    (typed : ∀ x y z, R x y z → A x ∧ B y ∧ D z)
    (sub : ∀ d, TernaryImage E R d → TernaryImage E S d) : TernaryExtends S R := by
  intro x y z hr
  obtain ⟨hx,hy,hz⟩ := typed x y z hr
  obtain ⟨d,hd,he⟩ := total x y z hx hy hz
  obtain ⟨u,v,w,hs,hf⟩ := sub d ⟨x,y,z,hr,he⟩
  obtain ⟨eu,ev,ew⟩ := injective x y z u v w d he hf
  subst u; subst v; subst w
  exact hs

theorem rigidTernaryPower_embeds_power (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (E : α → β → γ → δ → Prop)
    (rc : P.RigidComprehension (δ → Prop))
    (typed : ∀ x y z d, E x y z d → J d)
    (total : ∀ x y z, A x → B y → D z → ∃ d, J d ∧ E x y z d)
    (injective : ∀ x y z u v w d, E x y z d → E u v w d → x = u ∧ y = v ∧ z = w) :
    Embeds (RigidTernaryPower A B D) (RigidPower J) := by
  apply rigidImageCode_embeds J J (RigidTernaryPower A B D) (TernaryImage E) rc (embeds_refl J)
  · intro R hR d h
    exact h.elim (fun x hx => hx.elim (fun y hy => hy.elim (fun z hz => typed x y z d hz.2)))
  · intro R S hR hS e
    exact ternaryExtends_antisymm R S hR.1 hS.1
      (ternaryImage_typed_reflect A B D J E total injective S R hS.2 (fun d => (e d).mpr))
      (ternaryImage_typed_reflect A B D J E total injective R S hR.2 (fun d => (e d).mp))

theorem triplePair_target (J : δ → Prop) (F : α → δ → Prop)
    (G : β → δ → Prop) (H : γ → δ → Prop) (Q : δ → δ → δ → Prop)
    (hq : PairingOn J Q) (x : α) (y : β) (z : γ) (d : δ)
    (h : TriplePair F G H Q x y z d) : J d := by
  obtain ⟨u,v,w,t,hF,hG,hH,hQ,hd⟩ := h
  exact (hq.1 t w d hd).2.2

theorem rigidTernaryPower_embeds_of_pairing (A : α → Prop) (B : β → Prop) (D : γ → Prop)
    (J : δ → Prop) (Q : δ → δ → δ → Prop) (hq : PairingOn J Q)
    (rc : P.RigidComprehension (δ → Prop))
    (hA : Embeds A J) (hB : Embeds B J) (hD : Embeds D J) :
    Embeds (RigidTernaryPower A B D) (RigidPower J) := by
  obtain ⟨F,hf⟩ := hA
  obtain ⟨G,hg⟩ := hB
  obtain ⟨H,hh⟩ := hD
  exact rigidTernaryPower_embeds_power A B D J (TriplePair F G H Q) rc
    (triplePair_target J F G H Q hq)
    (triplePair_total A B D J F G H Q hf hg hh hq)
    (triplePair_injective A B D J F G H Q hf hg hh hq)

#classicism_check ternaryImage_typed_reflect rigidTernaryPower_embeds_power triplePair_target rigidTernaryPower_embeds_of_pairing
#classicism_types ternaryImage_typed_reflect rigidTernaryPower_embeds_power triplePair_target rigidTernaryPower_embeds_of_pairing
end Classicism.MathematicalContingency
