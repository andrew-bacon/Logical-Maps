import Classicism.Results.MathematicalContingency.HartogsBounds
import Classicism.Results.MathematicalContingency.PairingAbsorption

/-! Ordered pairs represented by rigid singleton binary graphs.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def PairAt (A : α → Prop) (P : α → α → Prop) (x y : α) : Prop :=
  A x ∧ A y ∧ Rigid P ∧ ∀ u v, P u v ↔ u = x ∧ v = y

def PairCarrier (A : α → Prop) (P : α → α → Prop) : Prop := ∃ x y, PairAt A P x y

theorem pairAt_exists (A : α → Prop) (rc : P.RigidComprehension (α → α → Prop))
    (x y : α) (hx : A x) (hy : A y) : ∃ P, PairAt A P x y := by
  obtain ⟨P,hP,e⟩ := rc (fun u v => u = x ∧ v = y)
  exact ⟨P,hx,hy,hP,fun u v => (e u v).symm⟩

theorem pairAt_coordinates (A : α → Prop) (P : α → α → Prop) (x y u v : α)
    (h : PairAt A P x y) (k : PairAt A P u v) : x = u ∧ y = v :=
  (k.2.2.2 x y).mp ((h.2.2.2 x y).mpr ⟨rfl,rfl⟩)

theorem pairAt_unique (A : α → Prop) (P Q : α → α → Prop) (x y : α)
    (h : PairAt A P x y) (k : PairAt A Q x y) : P = Q :=
  rigid_eq_of_coext P Q h.2.2.1 k.2.2.1 (fun u v => (h.2.2.2 u v).trans (k.2.2.2 u v).symm)

theorem pairing_of_pairCarrier_embedding (A : α → Prop)
    (rc : P.RigidComprehension (α → α → Prop)) (emb : Embeds (PairCarrier A) A) :
    ∃ Q, PairingOn A Q := by
  obtain ⟨F,hF⟩ := emb
  refine ⟨fun x y z => ∃ P, PairAt A P x y ∧ F P z,?_,?_,?_,?_⟩
  · intro x y z ⟨P,hP,hz⟩
    exact ⟨hP.1,hP.2.1,(hF.1.1 P z hz).2⟩
  · intro x y hx hy
    obtain ⟨P,hP⟩ := pairAt_exists A rc x y hx hy
    obtain ⟨z,hz,hPz⟩ := hF.1.2.1 P ⟨x,y,hP⟩
    exact ⟨z,hz,P,hP,hPz⟩
  · intro x y z w ⟨P,hP,hz⟩ ⟨Q,hQ,hw⟩
    have e := pairAt_unique A P Q x y hP hQ
    subst Q
    exact hF.1.2.2 P z w hz hw
  · intro x y u v z ⟨P,hP,hz⟩ ⟨Q,hQ,hw⟩
    have e := hF.2 P Q z hz hw
    subst Q
    exact pairAt_coordinates A P x y u v hP hQ

theorem pairCarrier_embedding_of_pairing (A : α → Prop) (Q : α → α → α → Prop)
    (hq : PairingOn A Q) : Embeds (PairCarrier A) A := by
  refine ⟨fun P z => ∃ x y, PairAt A P x y ∧ Q x y z,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro P z ⟨x,y,hP,hz⟩
    exact ⟨⟨x,y,hP⟩,(hq.1 x y z hz).2.2⟩
  · intro P ⟨x,y,hP⟩
    obtain ⟨z,hz,hQ⟩ := hq.2.1 x y hP.1 hP.2.1
    exact ⟨z,hz,x,y,hP,hQ⟩
  · intro P z w ⟨x,y,hP,hz⟩ ⟨u,v,hP',hw⟩
    obtain ⟨ex,ey⟩ := pairAt_coordinates A P x y u v hP hP'
    subst u; subst v
    exact hq.2.2.1 x y z w hz hw
  · intro P R z ⟨x,y,hP,hz⟩ ⟨u,v,hR,hw⟩
    obtain ⟨ex,ey⟩ := hq.2.2.2 x y u v z hz hw
    subst u; subst v
    exact pairAt_unique A P R x y hP hR

theorem pairCarrier_embeds_from_coordinates (A : α → Prop) (B : β → Prop)
    (F : α → β → Prop) (Q : β → β → β → Prop) (hf : Injects F A B) (hq : PairingOn B Q) :
    Embeds (PairCarrier A) B := by
  refine ⟨fun P z => ∃ x y u v, PairAt A P x y ∧ F x u ∧ F y v ∧ Q u v z,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro P z ⟨x,y,u,v,hP,_,_,hz⟩
    exact ⟨⟨x,y,hP⟩,(hq.1 u v z hz).2.2⟩
  · intro P ⟨x,y,hP⟩
    obtain ⟨u,hu,hxu⟩ := hf.1.2.1 x hP.1
    obtain ⟨v,hv,hyv⟩ := hf.1.2.1 y hP.2.1
    obtain ⟨z,hz,hqz⟩ := hq.2.1 u v hu hv
    exact ⟨z,hz,x,y,u,v,hP,hxu,hyv,hqz⟩
  · intro P z w ⟨x,y,u,v,hP,hxu,hyv,hz⟩ ⟨x',y',u',v',hP',hxu',hyv',hw⟩
    obtain ⟨ex,ey⟩ := pairAt_coordinates A P x y x' y' hP hP'
    subst x'; subst y'
    have eu := hf.1.2.2 x u u' hxu hxu'
    have ev := hf.1.2.2 y v v' hyv hyv'
    subst u'; subst v'
    exact hq.2.2.1 u v z w hz hw
  · intro P R z ⟨x,y,u,v,hP,hxu,hyv,hz⟩ ⟨x',y',u',v',hR,hxu',hyv',hw⟩
    obtain ⟨eu,ev⟩ := hq.2.2.2 u v u' v' z hz hw
    subst u'; subst v'
    have ex := hf.2 x x' u hxu hxu'
    have ey := hf.2 y y' v hyv hyv'
    subst x'; subst y'
    exact pairAt_unique A P R x y hP hR

#classicism_check pairAt_exists pairAt_coordinates pairAt_unique pairing_of_pairCarrier_embedding pairCarrier_embedding_of_pairing pairCarrier_embeds_from_coordinates
#classicism_types pairAt_exists pairAt_coordinates pairAt_unique pairing_of_pairCarrier_embedding pairCarrier_embedding_of_pairing pairCarrier_embeds_from_coordinates
end Classicism.MathematicalContingency
