import Classicism.Results.MathematicalContingency.FiniteSetAbsorption
import Classicism.Results.MathematicalContingency.FiniteGraphCardinality
import Classicism.Results.MathematicalContingency.NaturalPairing

/-! Relational pairing supplies finite-subset and finite-graph cardinal bounds.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

def PairingOn (K : α → Prop) (Q : α → α → α → Prop) : Prop :=
  (∀ x y z, Q x y z → K x ∧ K y ∧ K z) ∧
  (∀ x y, K x → K y → ∃ z, K z ∧ Q x y z) ∧
  (∀ x y z w, Q x y z → Q x y w → z = w) ∧
  ∀ x y u v z, Q x y z → Q u v z → x = u ∧ y = v

theorem lowerPair_pairing {σ : Type} [Ty σ] (hp : LowerPeano σ) :
    PairingOn (@LowerNat σ _) LowerPair :=
  ⟨lowerPair_numbers,lowerPair_total,lowerPair_functional hp,lowerPair_injective hp⟩

theorem finitePower_absorption_of_pairing (K : α → Prop) (L : α → α → Prop)
    (Q : α → α → α → Prop) (hw : WellOrderOn K L) (hq : PairingOn K Q)
    (a b : α) (ha : K a) (hb : K b) (hne : a ≠ b) : Embeds (RigidFinitePower K) K := by
  obtain ⟨z,hz,hzQ⟩ := hq.2.1 a a ha ha
  let C : α → α → α → Prop := fun x c d => ∃ u, Q x c u ∧ Q b u d
  have total : ∀ x c, K x → K c → ∃ d, K d ∧ C x c d := by
    intro x c hx hc
    obtain ⟨u,hu,he⟩ := hq.2.1 x c hx hc
    obtain ⟨d,hd,hf⟩ := hq.2.1 b u hb hu
    exact ⟨d,hd,u,he,hf⟩
  have disjoint : ∀ x c, ¬ C x c z := by
    intro x c h
    obtain ⟨u,_,he⟩ := h
    exact hne ((hq.2.2.2 a a b u z hzQ he).1)
  have injective : ∀ x y c d v, C x c v → C y d v → x = y ∧ c = d := by
    intro x y c d v h1 h2
    obtain ⟨u,hxu,huv⟩ := h1
    obtain ⟨w,hyw,hwv⟩ := h2
    have e := (hq.2.2.2 b u b w v huv hwv).2
    subst w
    exact hq.2.2.2 x c y d u hxu hyw
  exact finitePower_absorption_of_constructors K z C L hw hz total disjoint injective

def TriplePair (F : α → δ → Prop) (G : β → δ → Prop) (H : γ → δ → Prop)
    (Q : δ → δ → δ → Prop) (x : α) (y : β) (z : γ) (k : δ) : Prop :=
  ∃ u v w t, F x u ∧ G y v ∧ H z w ∧ Q u v t ∧ Q t w k

variable (A : α → Prop) (B : β → Prop) (D : γ → Prop) (K : δ → Prop)
  (F : α → δ → Prop) (G : β → δ → Prop) (H : γ → δ → Prop) (Q : δ → δ → δ → Prop)

theorem triplePair_total (hf : Injects F A K) (hg : Injects G B K) (hh : Injects H D K)
    (hq : PairingOn K Q) :
    ∀ x y z, A x → B y → D z → ∃ k, K k ∧ TriplePair F G H Q x y z k := by
  intro x y z hx hy hz
  obtain ⟨u,hu,hxu⟩ := hf.1.2.1 x hx
  obtain ⟨v,hv,hyv⟩ := hg.1.2.1 y hy
  obtain ⟨w,hw,hzw⟩ := hh.1.2.1 z hz
  obtain ⟨t,ht,huvt⟩ := hq.2.1 u v hu hv
  obtain ⟨k,hk,htwk⟩ := hq.2.1 t w ht hw
  exact ⟨k,hk,u,v,w,t,hxu,hyv,hzw,huvt,htwk⟩

theorem triplePair_functional (hf : Injects F A K) (hg : Injects G B K) (hh : Injects H D K)
    (hq : PairingOn K Q) :
    ∀ x y z k l, TriplePair F G H Q x y z k → TriplePair F G H Q x y z l → k = l := by
  intro x y z k l ⟨u,v,w,t,hxu,hyv,hzw,hqt,hqk⟩ ⟨u',v',w',t',hxu',hyv',hzw',hqt',hql⟩
  have eu := hf.1.2.2 x u u' hxu hxu'
  have ev := hg.1.2.2 y v v' hyv hyv'
  have ew := hh.1.2.2 z w w' hzw hzw'
  subst u'; subst v'; subst w'
  have et := hq.2.2.1 u v t t' hqt hqt'
  subst t'
  exact hq.2.2.1 t w k l hqk hql

theorem triplePair_injective (hf : Injects F A K) (hg : Injects G B K) (hh : Injects H D K)
    (hq : PairingOn K Q) :
    ∀ x y z x' y' z' k, TriplePair F G H Q x y z k → TriplePair F G H Q x' y' z' k →
      x = x' ∧ y = y' ∧ z = z' := by
  intro x y z x' y' z' k ⟨u,v,w,t,hxu,hyv,hzw,hqt,hqk⟩ ⟨u',v',w',t',hxu',hyv',hzw',hqt',hqk'⟩
  obtain ⟨et,ew⟩ := hq.2.2.2 t w t' w' k hqk hqk'
  subst t'; subst w'
  obtain ⟨eu,ev⟩ := hq.2.2.2 u v u' v' t hqt hqt'
  subst u'; subst v'
  exact ⟨hf.2 x x' u hxu hxu',hg.2 y y' v hyv hyv',hh.2 z z' w hzw hzw'⟩

theorem finiteCondition_bound_of_pairing (rc : P.RigidComprehension (δ → Prop))
    (L : δ → δ → Prop) (hw : WellOrderOn K L) (hq : PairingOn K Q)
    (a b : δ) (ha : K a) (hb : K b) (hne : a ≠ b)
    (hA : Embeds A K) (hB : Embeds B K) (hD : Embeds D K) : Embeds (FiniteCondition A B D) K := by
  obtain ⟨F,hf⟩ := hA
  obtain ⟨G,hg⟩ := hB
  obtain ⟨H,hh⟩ := hD
  exact finiteCondition_cardinal_bound A B D K (TriplePair F G H Q) rc
    (triplePair_total A B D K F G H Q hf hg hh hq)
    (triplePair_functional A B D K F G H Q hf hg hh hq)
    (triplePair_injective A B D K F G H Q hf hg hh hq)
    (finitePower_absorption_of_pairing K L Q hw hq a b ha hb hne)

#classicism_check lowerPair_pairing finitePower_absorption_of_pairing triplePair_total triplePair_functional triplePair_injective finiteCondition_bound_of_pairing
#classicism_types lowerPair_pairing finitePower_absorption_of_pairing triplePair_total triplePair_functional triplePair_injective finiteCondition_bound_of_pairing
end Classicism.MathematicalContingency
