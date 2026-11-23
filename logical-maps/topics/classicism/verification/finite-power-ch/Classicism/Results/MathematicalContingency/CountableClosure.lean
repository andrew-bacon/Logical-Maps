import Classicism.Results.MathematicalContingency.NaturalRecursion
import Classicism.Results.MathematicalContingency.SerialCounting

/-! Countably closed well-orderable orders meet countable dense downward families.
All sequences are relations on LowerNat. The fixed well-order supplies unique steps. -/
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]

def CountablyClosed (A : τ → Prop) (E : τ → τ → Prop) : Prop :=
  ∀ F : ((σ → Prop) → Prop) → τ → Prop, Maps F LowerNat A →
    (∀ n a b, LowerNat n → F n a → F (SucCard n) b → E b a) →
    ∃ c, A c ∧ ∀ n a, F n a → E c a

def LeastDenseStep (A : τ → Prop) (E L : τ → τ → Prop)
    (D : ((σ → Prop) → Prop) → τ → Prop) (n : (σ → Prop) → Prop) (a b : τ) : Prop :=
  LeastRelated A A L (fun a b => E b a ∧ D n b) a b

theorem leastDenseStep_total (A : τ → Prop) (E L : τ → τ → Prop)
    (D : ((σ → Prop) → Prop) → τ → Prop) (hw : WellOrderOn A L)
    (dense : ∀ n a, LowerNat n → A a → ∃ b, A b ∧ E b a ∧ D n b)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) (a : τ) (ha : A a) :
    ∃ b, A b ∧ LeastDenseStep A E L D n a b := by
  obtain ⟨b,hb⟩ := leastRelated_exists A A L (fun a b => E b a ∧ D n b) hw
    (fun a ha => dense n a hn ha) a ha
  exact ⟨b,hb.2.1,hb⟩

theorem leastDenseStep_functional (A : τ → Prop) (E L : τ → τ → Prop)
    (D : ((σ → Prop) → Prop) → τ → Prop) (hw : WellOrderOn A L)
    (n : (σ → Prop) → Prop) (a b c : τ)
    (hb : LeastDenseStep A E L D n a b) (hc : LeastDenseStep A E L D n a c) : b = c :=
  leastRelated_unique A A L (fun a b => E b a ∧ D n b) hw a b c hb hc

theorem natRun_descending (hp : LowerPeano σ) (A : τ → Prop) (E L : τ → τ → Prop)
    (D : ((σ → Prop) → Prop) → τ → Prop) (hw : WellOrderOn A L)
    (z : τ) (n : (σ → Prop) → Prop) (hn : LowerNat n) (a b : τ)
    (ha : NatRun (LeastDenseStep A E L D) z n a)
    (hb : NatRun (LeastDenseStep A E L D) z (SucCard n) b) : E b a ∧ D n b := by
  obtain h | ⟨i,x,hi,hx,ht,e⟩ := natRun_cases (LeastDenseStep A E L D) z b _ hb
  · exact (lowerNat_suc_ne_zero hp n hn h.1).elim
  · have ei := hp.2 n i hn hi e
    subst i
    have ex := natRun_functional hp (LeastDenseStep A E L D) z
      (fun n a b c _ hb hc => leastDenseStep_functional A E L D hw n a b c hb hc) n hn x a hx ha
    subst x
    exact ht.2.2.1

/-- Fusion below a specified starting condition. No form of Choice is used. -/
theorem countablyClosed_dense_family (hp : LowerPeano σ)
    (A : τ → Prop) (E L : τ → τ → Prop)
    (D : ((σ → Prop) → Prop) → τ → Prop)
    (hw : WellOrderOn A L) (hc : @CountablyClosed σ τ _ _ A E)
    (dense : ∀ n a, LowerNat n → A a → ∃ b, A b ∧ E b a ∧ D n b)
    (down : ∀ n a b, LowerNat n → A a → A b → E b a → D n a → D n b)
    (z : τ) (hz : A z) : ∃ c, A c ∧ E c z ∧ ∀ n, LowerNat n → D n c := by
  have hm : Maps (NatRun (LeastDenseStep A E L D) z) LowerNat A :=
    natRun_maps hp A (LeastDenseStep A E L D) z hz
      (fun _ _ _ _ _ ht => ht.2.1)
      (fun n a hn ha => leastDenseStep_total A E L D hw dense n hn a ha)
      (fun n a b c _ hb hc => leastDenseStep_functional A E L D hw n a b c hb hc)
  obtain ⟨c,hcA,hbound⟩ := hc (NatRun (LeastDenseStep A E L D) z) hm
    (fun n a b hn ha hb => (natRun_descending hp A E L D hw z n hn a b ha hb).1)
  refine ⟨c,hcA,hbound _ z (natRun_zero _ z),?_⟩
  intro n hn
  obtain ⟨a,_,ha⟩ := hm.2.1 n hn
  obtain ⟨b,hbA,hb⟩ := hm.2.1 (SucCard n) (lowerNat_suc n hn)
  exact down n b c hn hbA hcA (hbound _ b hb)
    (natRun_descending hp A E L D hw z n hn a b ha hb).2

#classicism_check leastDenseStep_total leastDenseStep_functional natRun_descending countablyClosed_dense_family
#classicism_types leastDenseStep_total leastDenseStep_functional natRun_descending countablyClosed_dense_family
end Classicism.MathematicalContingency
