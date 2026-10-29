import Classicism.Results.MathematicalContingency.Arithmetic

/-! Relational recursion on LowerNat, without choice or native data recursion. -/
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]

def NatRun (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z : τ)
    (n : (σ → Prop) → Prop) (x : τ) : Prop :=
  ∀ R : ((σ → Prop) → Prop) → τ → Prop, R (AtLeastZero σ) z →
    (∀ i a b, LowerNat i → R i a → T i a b → R (SucCard i) b) → R n x

theorem natRun_zero (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z : τ) :
    NatRun T z (AtLeastZero σ) z := fun _ hz _ => hz

theorem natRun_step (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z a b : τ)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) (h : NatRun T z n a) (ht : T n a b) :
    NatRun T z (SucCard n) b := fun R hz hs => hs n a b hn (h R hz hs) ht

theorem natRun_data (A : τ → Prop) (T : ((σ → Prop) → Prop) → τ → τ → Prop)
    (z : τ) (hz : A z) (closed : ∀ n a b, LowerNat n → A a → T n a b → A b)
    (n : (σ → Prop) → Prop) (x : τ) (h : NatRun T z n x) : LowerNat n ∧ A x :=
  h (fun i a => LowerNat i ∧ A a) ⟨lowerNat_zero,hz⟩
    (fun i a b hi ih ht => ⟨lowerNat_suc i hi,closed i a b hi ih.2 ht⟩)

theorem natRun_cases (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z x : τ)
    (n : (σ → Prop) → Prop) (h : NatRun T z n x) :
    (n = AtLeastZero σ ∧ x = z) ∨
      ∃ i a, LowerNat i ∧ NatRun T z i a ∧ T i a x ∧ n = SucCard i := by
  have hh := h (fun n x => NatRun T z n x ∧ ((n = AtLeastZero σ ∧ x = z) ∨
      ∃ i a, LowerNat i ∧ NatRun T z i a ∧ T i a x ∧ n = SucCard i))
    ⟨natRun_zero T z,Or.inl ⟨rfl,rfl⟩⟩
    (fun i a b hi ih ht => ⟨natRun_step T z a b i hi ih.1 ht,
      Or.inr ⟨i,a,hi,ih.1,ht,rfl⟩⟩)
  exact hh.2

theorem natRun_total (A : τ → Prop) (T : ((σ → Prop) → Prop) → τ → τ → Prop)
    (z : τ) (hz : A z) (total : ∀ n a, LowerNat n → A a → ∃ b, A b ∧ T n a b)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) : ∃ x, A x ∧ NatRun T z n x := by
  apply lowerNat_induction (fun i => ∃ x, A x ∧ NatRun T z i x) ?_ ?_ n hn
  · exact ⟨z,hz,natRun_zero T z⟩
  · intro i hi ih
    obtain ⟨a,ha,hr⟩ := ih
    obtain ⟨b,hb,ht⟩ := total i a hi ha
    exact ⟨b,hb,natRun_step T z a b i hi hr ht⟩

theorem natRun_functional (hp : LowerPeano σ)
    (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z : τ)
    (functional : ∀ n a b c, LowerNat n → T n a b → T n a c → b = c)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    ∀ a b, NatRun T z n a → NatRun T z n b → a = b := by
  apply lowerNat_induction (fun n => ∀ a b, NatRun T z n a → NatRun T z n b → a = b) ?_ ?_ n hn
  · intro a b ha hb
    obtain ea | ⟨i,x,hi,_,_,ei⟩ := natRun_cases T z a _ ha
    · obtain eb | ⟨j,y,hj,_,_,ej⟩ := natRun_cases T z b _ hb
      · exact ea.2.trans eb.2.symm
      · exact (hp.1 j hj ej).elim
    · exact (hp.1 i hi ei).elim
  · intro i hi ih a b ha hb
    obtain ea | ⟨j,x,hj,hx,ht,ej⟩ := natRun_cases T z a _ ha
    · exact (lowerNat_suc_ne_zero hp i hi ea.1).elim
    · have e := hp.2 i j hi hj ej
      subst j
      obtain eb | ⟨k,y,hk,hy,hu,ek⟩ := natRun_cases T z b _ hb
      · exact (lowerNat_suc_ne_zero hp i hi eb.1).elim
      · have e := hp.2 i k hi hk ek
        subst k
        have ex := ih x y hx hy
        subst y
        exact functional i x a b hi ht hu

theorem natRun_maps (hp : LowerPeano σ) (A : τ → Prop)
    (T : ((σ → Prop) → Prop) → τ → τ → Prop) (z : τ) (hz : A z)
    (closed : ∀ n a b, LowerNat n → A a → T n a b → A b)
    (total : ∀ n a, LowerNat n → A a → ∃ b, A b ∧ T n a b)
    (functional : ∀ n a b c, LowerNat n → T n a b → T n a c → b = c) :
    Maps (NatRun T z) LowerNat A :=
  ⟨fun n x h => natRun_data A T z hz closed n x h,
    fun n hn => natRun_total A T z hz total n hn,
    fun n a b ha hb => natRun_functional hp T z functional n
      (natRun_data A T z hz closed n a ha).1 a b ha hb⟩

#classicism_check natRun_zero natRun_step natRun_data natRun_cases natRun_total natRun_functional natRun_maps
#classicism_types natRun_zero natRun_step natRun_data natRun_cases natRun_total natRun_functional natRun_maps
end Classicism.MathematicalContingency
