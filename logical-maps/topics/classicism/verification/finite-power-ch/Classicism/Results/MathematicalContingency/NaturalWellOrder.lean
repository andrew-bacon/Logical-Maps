import Classicism.Results.MathematicalContingency.NaturalOrder
import Classicism.Results.MathematicalContingency.CarrierTheory

/-! Current well-order of the at-least naturals.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem lowerLT_suc_iff_le (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) : LowerLT m (SucCard n) ↔ LowerLE m n :=
  ((lowerLT_iff_suc_le hp m (SucCard n) hm (lowerNat_suc n hn)).trans
    (lowerLE_suc_iff hp m n hm hn))

theorem lowerNat_strictOrder (hp : LowerPeano σ) : StrictOrderOn (@LowerNat σ _) LowerLT :=
  ⟨fun _ _ h => ⟨h.1.1,h.1.2.1⟩,fun n _ => lowerLT_irrefl n,
    fun a b c _ _ _ => lowerLT_trans hp a b c,
    fun a b ha hb => (lowerLT_trichotomy a b ha hb).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))⟩

theorem lowerNat_minimum (hp : LowerPeano σ) (X : ((σ → Prop) → Prop) → Prop)
    (hX : ∀ n, X n → LowerNat n) (he : ∃ n, X n) :
    ∃ n, X n ∧ ∀ m, X m → ¬ LowerLT m n := by
  have main : ∀ n, LowerNat n →
      (∃ k, X k ∧ ∀ m, X m → ¬ LowerLT m k) ∨ (∀ k, LowerLE k n → ¬ X k) := by
    apply lowerNat_induction
    · obtain hz | hz := em (X (AtLeastZero σ))
      · exact Or.inl ⟨AtLeastZero σ,hz,fun m _ h => h.2 ((lowerLE_zero_iff hp m).mp h.1)⟩
      · exact Or.inr (fun k hk hx => hz (((lowerLE_zero_iff hp k).mp hk) ▸ hx))
    · intro n hn ih
      obtain he | hnX := ih
      · exact Or.inl he
      · obtain hs | hs := em (X (SucCard n))
        · exact Or.inl ⟨SucCard n,hs,fun m hm h => hnX m
            ((lowerLT_suc_iff_le hp m n (hX m hm) hn).mp h) hm⟩
        · refine Or.inr ?_
          intro k hk hx
          obtain e | e := em (k = SucCard n)
          · exact hs (e ▸ hx)
          · exact hnX k ((lowerLT_suc_iff_le hp k n (hX k hx) hn).mp ⟨hk,e⟩) hx
  obtain ⟨n,hn⟩ := he
  exact (main n (hX n hn)).elim id (fun h => (h n (lowerLE_refl n (hX n hn)) hn).elim)

theorem lowerNat_wellOrder (hp : LowerPeano σ) : WellOrderOn (@LowerNat σ _) LowerLT :=
  ⟨lowerNat_strictOrder hp,lowerNat_minimum hp⟩

theorem lowerNat_no_last (hp : LowerPeano σ) :
    ∀ n : (σ → Prop) → Prop, LowerNat n → ∃ m, LowerNat m ∧ LowerLT n m :=
  fun n hn => ⟨SucCard n,lowerNat_suc n hn,lowerLT_suc hp n hn⟩

#classicism_check lowerLT_suc_iff_le lowerNat_strictOrder lowerNat_minimum lowerNat_wellOrder lowerNat_no_last
#classicism_types lowerLT_suc_iff_le lowerNat_strictOrder lowerNat_minimum lowerNat_wellOrder lowerNat_no_last
end Classicism.MathematicalContingency
