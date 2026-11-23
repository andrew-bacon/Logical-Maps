import Classicism.Results.MathematicalContingency.PairingTransport

/-! Finite-Power CH Strategy: power codes represent extensions, not predicates.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
All comparisons and transports are actual relations. No choice or RC is used.
-/
namespace Classicism.MathematicalContingency.FinitePower
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

def RepresentsPower (R : γ → α → Prop) (C : γ → Prop) (A : α → Prop) : Prop :=
  (∀ c a, R c a → C c ∧ A a) ∧
  (∀ c d, C c → C d → (∀ a, R c a ↔ R d a) → c = d) ∧
  ∀ Z : α → Prop, (∀ a, Z a → A a) → ∃ c, C c ∧ ∀ a, R c a ↔ Z a

def Pow (C : γ → Prop) (A : α → Prop) : Prop := ∃ R, RepresentsPower R C A

theorem powerCodes_bijects (A : α → Prop) (C : γ → Prop) (D : δ → Prop)
    (R : γ → α → Prop) (S : δ → α → Prop)
    (hr : RepresentsPower R C A) (hs : RepresentsPower S D A) :
    Bijects (fun c d => C c ∧ D d ∧ ∀ a, R c a ↔ S d a) C D := by
  have maps : Maps (fun c d => C c ∧ D d ∧ ∀ a, R c a ↔ S d a) C D := by
    refine ⟨fun _ _ h => ⟨h.1,h.2.1⟩,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,e⟩ := hs.2.2 (R c) (fun a h => (hr.1 c a h).2)
      exact ⟨d,hd,hc,hd,fun a => (e a).symm⟩
    · intro c d f hd hf
      exact hs.2.1 d f hd.2.1 hf.2.1 (fun a => (hd.2.2 a).symm.trans (hf.2.2 a))
  refine ⟨⟨maps,?_⟩,maps,?_⟩
  · intro c d f hc hd
    exact hr.2.1 c d hc.1 hd.1 (fun a => (hc.2.2 a).trans (hd.2.2 a).symm)
  · intro d hd
    obtain ⟨c,hc,e⟩ := hr.2.2 (S d) (fun a h => (hs.1 d a h).2)
    exact ⟨c,hc,hc,hd,e⟩

theorem pow_equinumerous (A : α → Prop) (C : γ → Prop) (D : δ → Prop)
    (hc : Pow C A) (hd : Pow D A) : Equinumerous C D := by
  obtain ⟨R,hr⟩ := hc
  obtain ⟨S,hs⟩ := hd
  exact ⟨_,powerCodes_bijects A C D R S hr hs⟩

/-- Pull rows back along a displayed bijection. An arbitrary subcollection is
represented through its relational image; no representative is selected. -/
theorem representsPower_pullback (A : α → Prop) (B : β → Prop) (C : γ → Prop)
    (F : α → β → Prop) (R : γ → β → Prop)
    (hf : Bijects F A B) (hr : RepresentsPower R C B) :
    RepresentsPower (fun c a => ∃ b, F a b ∧ R c b) C A := by
  refine ⟨?_,?_,?_⟩
  · intro c a ⟨b,hf',hr'⟩
    exact ⟨(hr.1 c b hr').1,(hf.1.1.1 a b hf').1⟩
  · intro c d hc hd e
    apply hr.2.1 c d hc hd
    intro b
    constructor
    · intro h
      obtain ⟨a,_,hab⟩ := hf.2.2 b (hr.1 c b h).2
      obtain ⟨v,hav,hdv⟩ := (e a).mp ⟨b,hab,h⟩
      exact (hf.1.1.2.2 a v b hav hab) ▸ hdv
    · intro h
      obtain ⟨a,_,hab⟩ := hf.2.2 b (hr.1 d b h).2
      obtain ⟨v,hav,hcv⟩ := (e a).mpr ⟨b,hab,h⟩
      exact (hf.1.1.2.2 a v b hav hab) ▸ hcv
  · intro Z sub
    obtain ⟨c,hc,e⟩ := hr.2.2 (fun b => ∃ a, Z a ∧ F a b)
      (fun b h => h.elim (fun a ha => (hf.1.1.1 a b ha.2).2))
    refine ⟨c,hc,?_⟩
    intro a
    constructor
    · intro ⟨b,hab,hcb⟩
      obtain ⟨x,hx,hxb⟩ := (e b).mp hcb
      exact (hf.1.2 x a b hxb hab) ▸ hx
    · intro ha
      obtain ⟨b,_,hab⟩ := hf.1.1.2.1 a (sub a ha)
      exact ⟨b,hab,(e b).mpr ⟨a,ha,hab⟩⟩

theorem pow_pullback (A : α → Prop) (B : β → Prop) (C : γ → Prop)
    (F : α → β → Prop) (hf : Bijects F A B) (power : Pow C B) : Pow C A := by
  obtain ⟨R,hr⟩ := power
  exact ⟨_,representsPower_pullback A B C F R hf hr⟩

/-- Cross-type collections can be replaced by the image of an injection. -/
theorem pow_transfer_from_image (A : α → Prop) (Y : β → Prop) (C : γ → Prop)
    (F : α → β → Prop) (hf : Injects F A Y) (power : Pow C (RelImage F)) : Pow C A :=
  pow_pullback A (RelImage F) C F (injects_bijects_image A Y F hf) power

#classicism_check powerCodes_bijects pow_equinumerous representsPower_pullback pow_pullback pow_transfer_from_image
#classicism_types powerCodes_bijects pow_equinumerous representsPower_pullback pow_pullback pow_transfer_from_image
end Classicism.MathematicalContingency.FinitePower
