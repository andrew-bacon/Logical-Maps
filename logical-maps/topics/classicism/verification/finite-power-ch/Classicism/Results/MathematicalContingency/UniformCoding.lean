import Classicism.Results.MathematicalContingency.FiniteLayerCoding
import Classicism.Results.MathematicalContingency.BoundedAntichains
import Classicism.Results.MathematicalContingency.ConeAntichains
namespace Classicism.MathematicalContingency
variable {σ α β η τ : Type} [Ty σ] [Ty α] [Ty β] [Ty η] [Ty τ]

/-- A single formula supplies all fibre injections; no choice principle is used. -/
theorem finiteLayers_uniform (hp : LowerPeano σ) (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (J : η → Prop) (U : η → α → Prop)
    (D : η → ((σ → Prop) → Prop) → α → Prop)
    (finite : ∀ t, J t → ∀ n, LowerNat n → FiniteSubset A (D t n))
    (cover : ∀ t, J t → ∀ x, U t x → ∃ n, LowerNat n ∧ D t n x) :
    ∃ T : η → α → ((σ → Prop) → Prop) → Prop,
      ∀ t, J t → Injects (T t) (U t) (@LowerNat σ _) :=
  ⟨fun t => LayerCode (U t) L (D t),
    fun t ht => finiteLayers_injects hp A (U t) L (D t) hw (finite t ht) (cover t ht)⟩

/-- Transfer uniform injections from incompatible conditions to nonzero antichains. -/
theorem denseCones_uniform_countable (Q : α → Prop) (E L : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop)
    (hq : PartialOrderOn Q E) (hb : PartialOrderOn B R) (hw : WellOrderOn Q L)
    (hc : DenseCones Q E B R o C) (J : η → Prop) (U : η → β → Prop)
    (hu : ∀ t, J t → NonzeroAntichain B R o (U t))
    (count : ∀ V : η → α → Prop,
      (∀ t, J t → ∀ q, V t q → Q q) →
      (∀ t, J t → ∀ q r, V t q → V t r → q ≠ r → ¬ ∃ s, Q s ∧ E s q ∧ E s r) →
      ∃ T : η → α → ((σ → Prop) → Prop) → Prop,
        ∀ t, J t → Injects (T t) (V t) (@LowerNat σ _)) :
    ∃ T : η → β → ((σ → Prop) → Prop) → Prop,
      ∀ t, J t → Injects (T t) (U t) (@LowerNat σ _) := by
  obtain ⟨T,hT⟩ := count (fun t => SelectedCones Q L R C (U t))
    (fun _ _ q h => h.elim (fun _ h => h.2.1))
    (fun t ht q r hq hr hn => selectedCones_incompatible Q E L B R o C (U t) hb hw hc (hu t ht) q r hq hr hn)
  exact ⟨fun t => RelCompose (LeastCone Q L R C (U t)) (T t),
    fun t ht => injects_compose _ _ (U t) (SelectedCones Q L R C (U t)) LowerNat
      (leastCone_bijects Q E L B R o C (U t) hq hb hw hc (hu t ht)).1 (hT t ht)⟩

/-- Uniform countability of incompatible Cohen families, with the code kept existential. -/
theorem cohenFamilies_countable (hp : LowerPeano σ) (I : τ → Prop)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (L : (((σ → Prop) → Prop) → τ → Prop → Prop) → (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop)
    (hw : WellOrderOn (CohenCondition I) L) (J : η → Prop)
    (U : η → (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop)
    (sub : ∀ t, J t → ∀ q, U t q → CohenCondition I q)
    (inc : ∀ t, J t → ∀ q r, U t q → U t r → q ≠ r →
      ¬ ∃ s, CohenCondition I s ∧ ConditionOrder LowerNat I ConditionBit s q ∧
        ConditionOrder LowerNat I ConditionBit s r) :
    ∃ T : η → (((σ → Prop) → Prop) → τ → Prop → Prop) → ((σ → Prop) → Prop) → Prop,
      ∀ t, J t → Injects (T t) (U t) (@LowerNat σ _) := by
  apply finiteLayers_uniform hp (CohenCondition I) L hw J U
    (fun t n q => U t q ∧ TernaryBound LowerNat I ConditionBit n q)
  · intro t ht n hn
    apply cohen_antichain_layer_finite hp I rc (U t) (sub t ht) ?_ n hn
    intro q r hq hr hne ⟨s,hs,hsq,hsr⟩
    exact inc t ht q r hq hr hne ⟨s,hs,⟨hs,sub t ht q hq,hsq⟩,⟨hs,sub t ht r hr,hsr⟩⟩
  · intro t ht q hq
    obtain ⟨n,hn,hbound⟩ := cohen_condition_has_bound I q (sub t ht q hq)
    exact ⟨n,hn,hq,hbound⟩

#classicism_check finiteLayers_uniform denseCones_uniform_countable cohenFamilies_countable
#classicism_types finiteLayers_uniform denseCones_uniform_countable cohenFamilies_countable
end Classicism.MathematicalContingency
