import Classicism.Results.MathematicalContingency.PairingAbsorption
import Classicism.Results.MathematicalContingency.OrdinalExistence

/-! Pair-coded reflexive graphs retain both the carrier and its strict order.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def PairedBinaryImage (Q : σ → σ → σ → Prop) (G : σ → σ → Prop) (z : σ) : Prop :=
  ∃ x y, G x y ∧ Q x y z

def ReflexiveOrderGraph (B : σ → Prop) (R : σ → σ → Prop) (x y : σ) : Prop :=
  B x ∧ B y ∧ (x = y ∨ R x y)

theorem pairedBinaryImage_reflect (A : σ → Prop) (Q : σ → σ → σ → Prop)
    (hq : PairingOn A Q) (G T : σ → σ → Prop)
    (typed : ∀ x y, G x y → A x ∧ A y)
    (images : ∀ z, PairedBinaryImage Q G z → PairedBinaryImage Q T z) :
    ∀ x y, G x y → T x y := by
  intro x y hxy
  obtain ⟨z,_,hqz⟩ := hq.2.1 x y (typed x y hxy).1 (typed x y hxy).2
  obtain ⟨u,v,ht,huv⟩ := images z ⟨x,y,hxy,hqz⟩
  obtain ⟨ex,ey⟩ := hq.2.2.2 u v x y z huv hqz
  subst u
  subst v
  exact ht

theorem reflexiveOrderGraph_iso (B D : σ → Prop) (R S : σ → σ → Prop)
    (hw : WellOrderOn B R) (hs : WellOrderOn D S)
    (graphs : ∀ x y, ReflexiveOrderGraph B R x y ↔ ReflexiveOrderGraph D S x y) :
    OrderIso (fun x y => B x ∧ x = y) B R D S := by
  have carriers : ∀ x, B x ↔ D x := by
    intro x
    exact ⟨fun hx => ((graphs x x).mp ⟨hx,hx,Or.inl rfl⟩).1,
      fun hx => ((graphs x x).mpr ⟨hx,hx,Or.inl rfl⟩).1⟩
  apply orderIso_of_coext B D R S carriers
  intro x y hx hy
  constructor
  · intro hxy
    have h := ((graphs x y).mp ⟨hx,hy,Or.inr hxy⟩).2.2
    exact h.elim (fun e => False.elim (hw.1.2.1 x hx (e.symm ▸ hxy))) (fun k => k)
  · intro hxy
    have h := ((graphs x y).mpr ⟨(carriers x).mp hx,(carriers y).mp hy,Or.inr hxy⟩).2.2
    exact h.elim (fun e => False.elim (hs.1.2.1 x ((carriers x).mp hx) (e.symm ▸ hxy))) (fun k => k)

theorem pairedReflexiveOrder_iso (A B D : σ → Prop) (Q : σ → σ → σ → Prop)
    (R S : σ → σ → Prop) (hq : PairingOn A Q)
    (subB : ∀ x, B x → A x) (subD : ∀ x, D x → A x)
    (hw : WellOrderOn B R) (hs : WellOrderOn D S)
    (codes : ∀ z, PairedBinaryImage Q (ReflexiveOrderGraph B R) z ↔
      PairedBinaryImage Q (ReflexiveOrderGraph D S) z) :
    OrderIso (fun x y => B x ∧ x = y) B R D S := by
  apply reflexiveOrderGraph_iso B D R S hw hs
  intro x y
  exact ⟨pairedBinaryImage_reflect A Q hq _ _
      (fun u v h => ⟨subB u h.1,subB v h.2.1⟩) (fun z => (codes z).mp) x y,
    pairedBinaryImage_reflect A Q hq _ _
      (fun u v h => ⟨subD u h.1,subD v h.2.1⟩) (fun z => (codes z).mpr) x y⟩

#classicism_check pairedBinaryImage_reflect reflexiveOrderGraph_iso pairedReflexiveOrder_iso
#classicism_types pairedBinaryImage_reflect reflexiveOrderGraph_iso pairedReflexiveOrder_iso
end Classicism.MathematicalContingency
