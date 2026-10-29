import Classicism.Results.MathematicalContingency.Arithmetic

/-! Relational addition laws for the paper's at-least naturals.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
These extend the checkpoint; upstream has the analogous recursion vocabulary
for exact cardinalities, but not these totality / algebra laws for LowerNat. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem lowerSum_induction (m : (σ → Prop) → Prop)
    (P : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (hz : P (AtLeastZero σ) m)
    (step : ∀ n k, LowerNat n → LowerNat k → LowerSum m n k → P n k →
      P (SucCard n) (SucCard k))
    (n k : (σ → Prop) → Prop) (h : LowerSum m n k) : P n k :=
  (h (fun n k => LowerSum m n k ∧ P n k) ⟨lowerSum_zero m,hz⟩
    (fun n k hn hk ih => ⟨lowerSum_suc m n k hn hk ih.1,step n k hn hk ih.1 ih.2⟩)).2

theorem lowerSum_zero_left (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    LowerSum (AtLeastZero σ) n n :=
  lowerNat_induction (fun n => LowerSum (AtLeastZero σ) n n) (lowerSum_zero _)
    (fun n hn ih => lowerSum_suc _ n n hn hn ih) n hn

theorem lowerSum_suc_left (m n k : (σ → Prop) → Prop)
    (h : LowerSum m n k) : LowerSum (SucCard m) n (SucCard k) :=
  lowerSum_induction m (fun n k => LowerSum (SucCard m) n (SucCard k))
    (lowerSum_zero _) (fun n k hn hk _ ih => lowerSum_suc _ n (SucCard k)
      hn (lowerNat_suc k hk) ih) n k h

theorem lowerSum_comm (m n k : (σ → Prop) → Prop) (hm : LowerNat m)
    (h : LowerSum m n k) : LowerSum n m k :=
  lowerSum_induction m (fun n k => LowerSum n m k) (lowerSum_zero_left m hm)
    (fun n k _ _ _ ih => lowerSum_suc_left n m k ih) n k h

theorem lowerSum_comm_iff (m n k : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) : LowerSum m n k ↔ LowerSum n m k :=
  ⟨lowerSum_comm m n k hm,lowerSum_comm n m k hn⟩

theorem lowerSum_zero_iff (hp : LowerPeano σ) (m k : (σ → Prop) → Prop) :
    LowerSum m (AtLeastZero σ) k ↔ k = m :=
  ⟨fun h => lowerSum_functional hp m _ lowerNat_zero k m h (lowerSum_zero m),
   fun h => h.symm ▸ lowerSum_zero m⟩

theorem lowerSum_suc_iff (hp : LowerPeano σ) (m n k : (σ → Prop) → Prop)
    (hn : LowerNat n) :
    LowerSum m (SucCard n) k ↔ ∃ l, LowerNat l ∧ LowerSum m n l ∧ k = SucCard l := by
  constructor
  · intro h
    obtain hz | ⟨a,b,ha,hb,hs,he,hk⟩ := lowerSum_cases m _ k h
    · exact (lowerNat_suc_ne_zero hp n hn hz.1).elim
    · have e := hp.2 n a hn ha he
      subst a
      exact ⟨b,hb,hs,hk⟩
  · intro ⟨l,hl,hs,he⟩
    exact he.symm ▸ lowerSum_suc m n l hn hl hs

/-- The associativity diagram: a+b=u and u+c=v yields b+c=w and a+w=v. -/
theorem lowerSum_assoc
    (a b u c v : (σ → Prop) → Prop) (hb : LowerNat b)
    (hab : LowerSum a b u) (huv : LowerSum u c v) :
    ∃ w, LowerNat w ∧ LowerSum b c w ∧ LowerSum a w v := by
  apply lowerSum_induction u (fun c v => ∃ w, LowerNat w ∧ LowerSum b c w ∧ LowerSum a w v)
    ⟨b,hb,lowerSum_zero b,hab⟩ ?_ c v huv
  intro n k hn hk _ ih
  obtain ⟨w,hw,hs,ht⟩ := ih
  exact ⟨SucCard w,lowerNat_suc w hw,lowerSum_suc b n w hn hw hs,
    lowerSum_suc a w k hw hk ht⟩

theorem lowerSum_cancel_left (hp : LowerPeano σ)
    (a b c k : (σ → Prop) → Prop) (ha : LowerNat a)
    (hb : LowerNat b) (hc : LowerNat c)
    (hab : LowerSum a b k) (hac : LowerSum a c k) : b = c := by
  have h : ∀ (a : (σ → Prop) → Prop), LowerNat a → ∀ (b c k : (σ → Prop) → Prop), LowerNat b → LowerNat c →
      LowerSum b a k → LowerSum c a k → b = c := by
    intro a ha
    apply lowerNat_induction _ ?_ ?_ a ha
    · intro b c k hb hc hb0 hc0
      exact ((lowerSum_zero_iff hp b k).mp hb0).symm.trans ((lowerSum_zero_iff hp c k).mp hc0)
    · intro a ha ih b c k hb hc hbk hck
      obtain ⟨u,hu,hbu,hku⟩ := (lowerSum_suc_iff hp b a k ha).mp hbk
      obtain ⟨v,hv,hcv,hkv⟩ := (lowerSum_suc_iff hp c a k ha).mp hck
      have e := hp.2 u v hu hv (hku.symm.trans hkv)
      subst v
      exact ih b c u hb hc hbu hcv
  exact h a ha b c k hb hc (lowerSum_comm a b k ha hab) (lowerSum_comm a c k ha hac)

#classicism_check lowerSum_induction lowerSum_zero_left lowerSum_suc_left lowerSum_comm
  lowerSum_comm_iff lowerSum_zero_iff lowerSum_suc_iff lowerSum_assoc lowerSum_cancel_left
#classicism_types lowerSum_induction lowerSum_zero_left lowerSum_suc_left lowerSum_comm
  lowerSum_comm_iff lowerSum_zero_iff lowerSum_suc_iff lowerSum_assoc lowerSum_cancel_left
end Classicism.MathematicalContingency
