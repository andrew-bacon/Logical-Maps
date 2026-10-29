import Classicism.Results.MathematicalContingency.CountableClosure
import Classicism.Results.MathematicalContingency.NaturalOrder

namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]

/-- Successor descent extends to the additive order, without choosing sequence values. -/
theorem descending_maps_antitone (A : τ → Prop) (E : τ → τ → Prop)
    (ho : PartialOrderOn A E) (F : ((σ → Prop) → Prop) → τ → Prop)
    (hf : Maps F LowerNat A)
    (step : ∀ n a b, LowerNat n → F n a → F (SucCard n) b → E b a)
    (m n : (σ → Prop) → Prop) (h : LowerLE m n)
    (a b : τ) (ha : F m a) (hb : F n b) : E b a := by
  obtain ⟨hm,hn,d,hd,hs⟩ := h
  have main : ∀ b, F n b → E b a := by
    apply lowerSum_induction m (fun _ k => ∀ b, F k b → E b a) ?_ ?_ d n hs
    · intro b hb
      have e := hf.2.2 m b a hb ha
      exact e.symm ▸ ho.2.1 a (hf.1 m a ha).2
    · intro j k hj hk hsum ih b hb
      obtain ⟨c,hcA,hc⟩ := hf.2.1 k hk
      exact ho.2.2.2 b c a (step k c b hk hc hb) (ih c hc)
  exact main b hb

theorem descending_maps_directed (A : τ → Prop) (E : τ → τ → Prop)
    (ho : PartialOrderOn A E) (F : ((σ → Prop) → Prop) → τ → Prop)
    (hf : Maps F LowerNat A)
    (step : ∀ n a b, LowerNat n → F n a → F (SucCard n) b → E b a)
    (i j : (σ → Prop) → Prop) (hi : LowerNat i) (hj : LowerNat j) :
    ∃ k c, LowerNat k ∧ F k c ∧
      (∀ a, F i a → E c a) ∧ (∀ b, F j b → E c b) := by
  obtain h | h := lowerLE_total i j hi hj
  · obtain ⟨c,hcA,hc⟩ := hf.2.1 j hj
    exact ⟨j,c,hj,hc,
      fun a ha => descending_maps_antitone A E ho F hf step i j h a c ha hc,
      fun b hb => descending_maps_antitone A E ho F hf step j j (lowerLE_refl j hj) b c hb hc⟩
  · obtain ⟨c,hcA,hc⟩ := hf.2.1 i hi
    exact ⟨i,c,hi,hc,
      fun a ha => descending_maps_antitone A E ho F hf step i i (lowerLE_refl i hi) a c ha hc,
      fun b hb => descending_maps_antitone A E ho F hf step j i h b c hb hc⟩

#classicism_check descending_maps_antitone descending_maps_directed
#classicism_types descending_maps_antitone descending_maps_directed
end Classicism.MathematicalContingency
