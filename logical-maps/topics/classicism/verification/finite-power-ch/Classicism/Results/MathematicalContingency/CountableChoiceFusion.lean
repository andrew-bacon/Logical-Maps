import Classicism.Results.MathematicalContingency.RelationalChoiceCarriers
import Classicism.Results.MathematicalContingency.CountableClosure

/-! Finite-Power CH Strategy: relational choice supplies the dense steps.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
No well-order of the forcing carrier is required. Choice is unboxed.
-/
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]

theorem natRun_successor_transition (hp : LowerPeano σ)
    (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z : τ)
    (functional : ∀ n a b c, LowerNat n → T n a b → T n a c → b = c)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) (a b : τ)
    (ha : NatRun T z n a) (hb : NatRun T z (SucCard n) b) : T n a b := by
  obtain h | ⟨i,x,hi,hx,ht,e⟩ := natRun_cases T z b _ hb
  · exact (lowerNat_suc_ne_zero hp n hn h.1).elim
  · have ei := hp.2 n i hn hi e
    subst i
    have ex := natRun_functional hp T z functional n hn x a hx ha
    subst x
    exact ht

/-- Fusion uses a selected relational transition, with no selection of a
function in Lean's metatheory. The initial condition supplies inhabitation. -/
theorem countablyClosed_dense_family_of_relationalChoice (hp : LowerPeano σ)
    (A : τ → Prop) (E : τ → τ → Prop)
    (D : ((σ → Prop) → Prop) → τ → Prop)
    (choice : P.RelationalChoice (((σ → Prop) → Prop) → τ → Prop) τ)
    (hc : @CountablyClosed σ τ _ _ A E)
    (dense : ∀ n a, LowerNat n → A a → ∃ b, A b ∧ E b a ∧ D n b)
    (down : ∀ n a b, LowerNat n → A a → A b → E b a → D n a → D n b)
    (z : τ) (hz : A z) : ∃ c, A c ∧ E c z ∧ ∀ n, LowerNat n → D n c := by
  obtain ⟨T,data,total,functional⟩ := relationalChoice_on_pairs LowerNat A A
    (fun n a b => E b a ∧ D n b) z choice dense
  have func : ∀ n a b c, LowerNat n → T n a b → T n a c → b = c :=
    fun n a b c _ hb hc => functional n a b c hb hc
  have hm : Maps (NatRun T z) LowerNat A :=
    natRun_maps hp A T z hz
      (fun n a b _ _ ht => (data n a b ht).2.2.1)
      (fun n a hn ha => (total n a hn ha).elim
        (fun b hb => ⟨b,(data n a b hb).2.2.1,hb⟩)) func
  have step : ∀ n a b, LowerNat n → NatRun T z n a →
      NatRun T z (SucCard n) b → E b a ∧ D n b :=
    fun n a b hn ha hb =>
      (data n a b (natRun_successor_transition hp T z func n hn a b ha hb)).2.2.2
  obtain ⟨c,hcA,bound⟩ := hc (NatRun T z) hm
    (fun n a b hn ha hb => (step n a b hn ha hb).1)
  refine ⟨c,hcA,bound _ z (natRun_zero T z),?_⟩
  intro n hn
  obtain ⟨a,_,ha⟩ := hm.2.1 n hn
  obtain ⟨b,hbA,hb⟩ := hm.2.1 (SucCard n) (lowerNat_suc n hn)
  exact down n b c hn hbA hcA (bound _ b hb) (step n a b hn ha hb).2

#classicism_check natRun_successor_transition countablyClosed_dense_family_of_relationalChoice
#classicism_types natRun_successor_transition countablyClosed_dense_family_of_relationalChoice
end Classicism.MathematicalContingency
