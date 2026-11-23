import Classicism.Results.MathematicalContingency.FrozenNameCarriers
import Classicism.Results.MathematicalContingency.HartogsDistinctness
import Classicism.Results.MathematicalContingency.RigidPairs
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

theorem bijects_inverse (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (h : Bijects F A B) : Bijects (fun y x => F x y) B A := by
  have hm : Maps (fun y x => F x y) B A :=
    ⟨fun y x hx => ⟨(h.1.1.1 x y hx).2,(h.1.1.1 x y hx).1⟩,
      h.2.2,fun y x z hx hz => h.1.2 x z y hx hz⟩
  exact ⟨⟨hm,fun y z x hy hz => h.1.1.2.2 x y z hy hz⟩,hm,h.1.1.2.1⟩

theorem bijects_target_coext (A : α → Prop) (B E : β → Prop) (F : α → β → Prop)
    (h : Bijects F A B) (he : E ≡ B) : Bijects F A E := by
  have hm : Maps F A E :=
    ⟨fun x y hx => ⟨(h.1.1.1 x y hx).1,(he y).mpr (h.1.1.1 x y hx).2⟩,
      fun x hx => (h.1.1.2.1 x hx).elim (fun y hy => ⟨y,(he y).mpr hy.1,hy.2⟩),h.1.1.2.2⟩
  exact ⟨⟨hm,h.1.2⟩,hm,fun y hy => h.2.2 y ((he y).mp hy)⟩

theorem bijects_image_wellOrder (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (L : α → α → Prop) (h : Bijects F A B) (hw : WellOrderOn A L) :
    WellOrderOn B (ImageOrder F L) :=
  wellOrder_coext (RelImage F) B (ImageOrder F L) (ImageOrder F L)
    (image_wellOrder F A B L h.1 hw)
    (fun y => ⟨fun hy => image_subset F A B h.1.1 y hy,
      fun hy => (h.2.2 y hy).elim (fun x hx => ⟨x,hx.2⟩)⟩)
    (fun _ _ => Iff.rfl)

/-- Mixed-type version of the existing rigid-pair coordinate coding construction. -/
theorem relProduct_embeds_from_coordinates (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (F : α → γ → Prop) (G : β → γ → Prop) (Q : γ → γ → γ → Prop)
    (hf : Injects F A K) (hg : Injects G B K) (hq : PairingOn K Q) :
    Embeds (RelProduct A B) K := by
  refine ⟨fun P z => ∃ x y u v, ProductPairAt A B P x y ∧ F x u ∧ G y v ∧ Q u v z,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro P z ⟨x,y,u,v,hP,_,_,hz⟩
    exact ⟨⟨x,y,hP⟩,(hq.1 u v z hz).2.2⟩
  · intro P ⟨x,y,hP⟩
    obtain ⟨u,hu,hxu⟩ := hf.1.2.1 x hP.1
    obtain ⟨v,hv,hyv⟩ := hg.1.2.1 y hP.2.1
    obtain ⟨z,hz,hqz⟩ := hq.2.1 u v hu hv
    exact ⟨z,hz,x,y,u,v,hP,hxu,hyv,hqz⟩
  · intro P z w ⟨x,y,u,v,hP,hxu,hyv,hz⟩ ⟨x',y',u',v',hP',hxu',hyv',hw⟩
    obtain ⟨ex,ey⟩ := productPairAt_coordinates A B P x x' y y' hP hP'
    subst x'; subst y'
    have eu := hf.1.2.2 x u u' hxu hxu'
    have ev := hg.1.2.2 y v v' hyv hyv'
    subst u'; subst v'
    exact hq.2.2.1 u v z w hz hw
  · intro P S z ⟨x,y,u,v,hP,hxu,hyv,hz⟩ ⟨x',y',u',v',hS,hxu',hyv',hw⟩
    obtain ⟨eu,ev⟩ := hq.2.2.2 u v u' v' z hz hw
    subst u'; subst v'
    have ex := hf.2 x x' u hxu hxu'
    have ey := hg.2 y y' v hyv hyv'
    subst x'; subst y'
    exact productPairAt_unique A B P S x y hP hS

theorem relProduct_embeds_of_pairing (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (Q : γ → γ → γ → Prop) (ha : Embeds A K) (hb : Embeds B K) (hq : PairingOn K Q) :
    Embeds (RelProduct A B) K :=
  ha.elim (fun F hf => hb.elim (fun G hg => relProduct_embeds_from_coordinates A B K F G Q hf hg hq))

/-- Transfer the coordinate cardinal gap through a name bijection and a product bound. -/
theorem nameCarrier_product_gap (A : α → Prop) (I K : β → Prop)
    (T : β → α → Prop → Prop) (E : (α → Prop) → Prop) (B : γ → Prop)
    (hI : Bijects (IndexedName A I T) I (NameCarrier A I T))
    (hK : Bijects (IndexedName A K T) K E)
    (Q : β → β → β → Prop) (hq : PairingOn K Q) (hb : Embeds B K)
    (large : ¬ Embeds I K) : ¬ Embeds (NameCarrier A I T) (RelProduct E B) := by
  have bound := relProduct_embeds_of_pairing E B K Q
    ⟨fun X a => IndexedName A K T a X,(bijects_inverse K E (IndexedName A K T) hK).1⟩ hb hq
  exact fun h => large (embeds_trans I (NameCarrier A I T) K
    ⟨IndexedName A I T,hI.1⟩ (embeds_trans (NameCarrier A I T) (RelProduct E B) K h bound))

#classicism_check bijects_inverse bijects_target_coext bijects_image_wellOrder relProduct_embeds_from_coordinates relProduct_embeds_of_pairing nameCarrier_product_gap
#classicism_types bijects_inverse bijects_target_coext bijects_image_wellOrder relProduct_embeds_from_coordinates relProduct_embeds_of_pairing nameCarrier_product_gap
end Classicism.MathematicalContingency
