import Classicism.Results.MathematicalContingency.NameCardinalTransport
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def PairingImage (F : α → β → Prop) (Q : α → α → α → Prop) (u v w : β) : Prop :=
  ∃ x y z, F x u ∧ F y v ∧ F z w ∧ Q x y z

theorem injects_bijects_image (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (h : Injects F A B) : Bijects F A (RelImage F) :=
  ⟨injects_into_image F A B h,(injects_into_image F A B h).1,
    fun y hy => hy.elim (fun x hx => ⟨x,(h.1.1 x y hx).1,hx⟩)⟩

theorem pairingImage_domains (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (Q : α → α → α → Prop) (hf : Maps F A B)
    (u v w : β) (h : PairingImage F Q u v w) : B u ∧ B v ∧ B w := by
  obtain ⟨x,y,z,hx,hy,hz,_⟩ := h
  exact ⟨(hf.1 x u hx).2,(hf.1 y v hy).2,(hf.1 z w hz).2⟩

theorem pairingImage_total (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (Q : α → α → α → Prop) (hf : Bijects F A B) (hq : PairingOn A Q)
    (u v : β) (hu : B u) (hv : B v) : ∃ w, B w ∧ PairingImage F Q u v w := by
  obtain ⟨x,hx,hxu⟩ := hf.2.2 u hu
  obtain ⟨y,hy,hyv⟩ := hf.2.2 v hv
  obtain ⟨z,hz,hqz⟩ := hq.2.1 x y hx hy
  obtain ⟨w,hw,hzw⟩ := hf.1.1.2.1 z hz
  exact ⟨w,hw,x,y,z,hxu,hyv,hzw,hqz⟩

theorem pairingImage_functional (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (Q : α → α → α → Prop) (hf : Injects F A B) (hq : PairingOn A Q)
    (u v w t : β) (h : PairingImage F Q u v w) (k : PairingImage F Q u v t) : w = t := by
  obtain ⟨x,y,z,hx,hy,hz,hqz⟩ := h
  obtain ⟨a,b,c,ha,hb,hc,hqc⟩ := k
  have ex := hf.2 x a u hx ha
  have ey := hf.2 y b v hy hb
  subst a; subst b
  have ez := hq.2.2.1 x y z c hqz hqc
  subst c
  exact hf.1.2.2 z w t hz hc

theorem pairingImage_injective (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (Q : α → α → α → Prop) (hf : Injects F A B) (hq : PairingOn A Q)
    (u v s t w : β) (h : PairingImage F Q u v w) (k : PairingImage F Q s t w) : u = s ∧ v = t := by
  obtain ⟨x,y,z,hx,hy,hz,hqz⟩ := h
  obtain ⟨a,b,c,ha,hb,hc,hqc⟩ := k
  have ez := hf.2 z c w hz hc
  subst c
  obtain ⟨ex,ey⟩ := hq.2.2.2 x y a b z hqz hqc
  subst a; subst b
  exact ⟨hf.1.2.2 x u s hx ha,hf.1.2.2 y v t hy hb⟩

theorem pairingImage_pairing (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (Q : α → α → α → Prop) (hf : Bijects F A B) (hq : PairingOn A Q) :
    PairingOn B (PairingImage F Q) :=
  ⟨pairingImage_domains A B F Q hf.1.1,pairingImage_total A B F Q hf hq,
    pairingImage_functional A B F Q hf.1 hq,pairingImage_injective A B F Q hf.1 hq⟩

#classicism_check injects_bijects_image pairingImage_domains pairingImage_total pairingImage_functional pairingImage_injective pairingImage_pairing
#classicism_types injects_bijects_image pairingImage_domains pairingImage_total pairingImage_functional pairingImage_injective pairingImage_pairing
end Classicism.MathematicalContingency
