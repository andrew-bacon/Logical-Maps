import Classicism.Results.MathematicalContingency.Multiplication

/-! The additive order on the paper's at-least naturals.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
This is an internal relational order, not an identification with Lean's Nat. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def LowerLE (m n : (σ → Prop) → Prop) : Prop :=
  LowerNat m ∧ LowerNat n ∧ ∃ d, LowerNat d ∧ LowerSum m d n

def LowerLT (m n : (σ → Prop) → Prop) : Prop := LowerLE m n ∧ m ≠ n

theorem lowerLE_refl (n : (σ → Prop) → Prop) (hn : LowerNat n) : LowerLE n n :=
  ⟨hn,hn,AtLeastZero σ,lowerNat_zero,lowerSum_zero n⟩

theorem lowerLE_zero (n : (σ → Prop) → Prop) (hn : LowerNat n) : LowerLE (AtLeastZero σ) n :=
  ⟨lowerNat_zero,hn,n,hn,lowerSum_zero_left n hn⟩

theorem lowerLE_step (m n : (σ → Prop) → Prop) (h : LowerLE m n) : LowerLE m (SucCard n) := by
  obtain ⟨hm,hn,d,hd,hs⟩ := h
  exact ⟨hm,lowerNat_suc n hn,SucCard d,lowerNat_suc d hd,lowerSum_suc m d n hd hn hs⟩

theorem lowerLE_suc (m n : (σ → Prop) → Prop) (h : LowerLE m n) :
    LowerLE (SucCard m) (SucCard n) := by
  obtain ⟨hm,hn,d,hd,hs⟩ := h
  exact ⟨lowerNat_suc m hm,lowerNat_suc n hn,d,hd,lowerSum_suc_left m d n hs⟩

theorem lowerLE_suc_iff (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) : LowerLE (SucCard m) (SucCard n) ↔ LowerLE m n := by
  constructor
  · intro ⟨_,_,d,hd,hs⟩
    obtain ⟨k,hk,hmk⟩ := lowerSum_total m d hm hd
    have e := lowerSum_functional hp (SucCard m) d hd (SucCard n) (SucCard k)
      hs (lowerSum_suc_left m d k hmk)
    have e := hp.2 n k hn hk e
    subst k
    exact ⟨hm,hn,d,hd,hmk⟩
  · exact lowerLE_suc m n

theorem lowerLE_trans (a b c : (σ → Prop) → Prop) (hab : LowerLE a b) (hbc : LowerLE b c) :
    LowerLE a c := by
  obtain ⟨ha,hb,u,hu,hs⟩ := hab
  obtain ⟨_,hc,v,hv,ht⟩ := hbc
  obtain ⟨w,hw,_,haw⟩ := lowerSum_assoc a u b v c hu hs ht
  exact ⟨ha,hc,w,hw,haw⟩

theorem lowerLE_antisymm (hp : LowerPeano σ) (a b : (σ → Prop) → Prop)
    (hab : LowerLE a b) (hba : LowerLE b a) : a = b := by
  obtain ⟨ha,hb,u,hu,hs⟩ := hab
  obtain ⟨_,_,v,hv,ht⟩ := hba
  obtain ⟨w,hw,huv,haw⟩ := lowerSum_assoc a u b v a hu hs ht
  have e := (lowerSum_self_iff hp a w ha hw).mp haw
  subst w
  have e := (lowerSum_eq_zero hp u v huv).1
  subst u
  exact ((lowerSum_zero_iff hp a b).mp hs).symm

theorem lowerLE_total (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n) :
    LowerLE m n ∨ LowerLE n m := by
  have main : ∀ (m : (σ → Prop) → Prop), LowerNat m → ∀ n, LowerNat n → LowerLE m n ∨ LowerLE n m := by
    intro m hm
    apply lowerNat_induction _ ?_ ?_ m hm
    · intro n hn
      exact Or.inl (lowerLE_zero n hn)
    · intro m hm ih n hn
      obtain e | ⟨k,hk,e⟩ := lowerNat_cases n hn
      · subst n
        exact Or.inr (lowerLE_zero _ (lowerNat_suc m hm))
      · subst n
        exact (ih k hk).elim (fun h => Or.inl (lowerLE_suc m k h))
          (fun h => Or.inr (lowerLE_suc k m h))
  exact main m hm n hn

theorem lowerLE_zero_iff (hp : LowerPeano σ) (n : (σ → Prop) → Prop) :
    LowerLE n (AtLeastZero σ) ↔ n = AtLeastZero σ :=
  ⟨fun ⟨_,_,d,_,hs⟩ => (lowerSum_eq_zero hp n d hs).1,
    fun e => e.symm ▸ lowerLE_refl (AtLeastZero σ) lowerNat_zero⟩

theorem lowerNat_ne_suc_self (hp : LowerPeano σ) (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    n ≠ SucCard n :=
  lowerNat_induction (fun n => n ≠ SucCard n) (hp.1 _ lowerNat_zero)
    (fun m hm ih e => ih (hp.2 m (SucCard m) hm (lowerNat_suc m hm) e)) n hn

theorem lowerLT_suc (hp : LowerPeano σ) (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    LowerLT n (SucCard n) :=
  ⟨lowerLE_step n n (lowerLE_refl n hn),lowerNat_ne_suc_self hp n hn⟩

theorem lowerLT_irrefl (n : (σ → Prop) → Prop) : ¬ LowerLT n n := fun h => h.2 rfl

theorem lowerLT_trans (hp : LowerPeano σ) (a b c : (σ → Prop) → Prop)
    (hab : LowerLT a b) (hbc : LowerLT b c) : LowerLT a c := by
  refine ⟨lowerLE_trans a b c hab.1 hbc.1,?_⟩
  intro e
  subst c
  exact hab.2 (lowerLE_antisymm hp a b hab.1 hbc.1)

theorem lowerLT_trichotomy (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n) :
    LowerLT m n ∨ m = n ∨ LowerLT n m := by
  obtain e | e := em (m = n)
  · exact Or.inr (Or.inl e)
  · exact (lowerLE_total m n hm hn).elim (fun h => Or.inl ⟨h,e⟩)
      (fun h => Or.inr (Or.inr ⟨h,fun he => e he.symm⟩))

theorem lowerLT_iff_suc_le (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) : LowerLT m n ↔ LowerLE (SucCard m) n := by
  constructor
  · intro ⟨⟨_,_,d,hd,hs⟩,hne⟩
    obtain e | ⟨k,hk,e⟩ := lowerNat_cases d hd
    · subst d
      exact (hne ((lowerSum_zero_iff hp m n).mp hs).symm).elim
    · subst d
      obtain ⟨l,hl,hml,e⟩ := (lowerSum_suc_iff hp m k n hk).mp hs
      subst n
      exact ⟨lowerNat_suc m hm,lowerNat_suc l hl,k,hk,lowerSum_suc_left m k l hml⟩
  · intro h
    have hstep := (lowerLT_suc hp m hm).1
    refine ⟨lowerLE_trans m (SucCard m) n hstep h,?_⟩
    intro e
    subst n
    exact lowerNat_ne_suc_self hp m hm (lowerLE_antisymm hp m (SucCard m) hstep h)

theorem lowerLE_add_right (hp : LowerPeano σ) (a b c u v : (σ → Prop) → Prop)
    (hc : LowerNat c) (hab : LowerLE a b) (hac : LowerSum a c u) (hbc : LowerSum b c v) :
    LowerLE u v := by
  obtain ⟨ha,hb,d,hd,had⟩ := hab
  obtain ⟨w,hw,hdc,haw⟩ := lowerSum_assoc a d b c v hd had hbc
  obtain ⟨x,hx,hax,hxd⟩ := lowerSum_assoc_left a c d w v ha hc hd
    (lowerSum_comm d c w hd hdc) haw
  have e := lowerSum_functional hp a c hc x u hax hac
  subst x
  exact ⟨(lowerSum_numbers a c u ha hac).2,(lowerSum_numbers b c v hb hbc).2,d,hd,hxd⟩

theorem lowerLE_mul_right (hp : LowerPeano σ) (a b c u v : (σ → Prop) → Prop)
    (hc : LowerNat c) (hab : LowerLE a b) (hac : LowerProd a c u) (hbc : LowerProd b c v) :
    LowerLE u v := by
  obtain ⟨ha,hb,d,hd,had⟩ := hab
  obtain ⟨w,hw,hdc⟩ := lowerProd_total d c hd hc
  have hu := (lowerProd_numbers a c u hac).2
  obtain ⟨t,ht,huw⟩ := lowerSum_total u w hu hw
  have hbt := lowerProd_distrib_right hp a d c b u w t ha hd hc had hac hdc huw
  have e := lowerProd_functional hp b c hc t v hbt hbc
  subst t
  exact ⟨hu,(lowerProd_numbers b c v hbc).2,w,hw,huw⟩

#classicism_check lowerLE_refl lowerLE_zero lowerLE_step lowerLE_suc lowerLE_suc_iff lowerLE_trans
  lowerLE_antisymm lowerLE_total lowerLE_zero_iff lowerNat_ne_suc_self lowerLT_suc lowerLT_irrefl
  lowerLT_trans lowerLT_trichotomy lowerLT_iff_suc_le lowerLE_add_right lowerLE_mul_right
#classicism_types lowerLE_refl lowerLE_zero lowerLE_step lowerLE_suc lowerLE_suc_iff lowerLE_trans
  lowerLE_antisymm lowerLE_total lowerLE_zero_iff lowerNat_ne_suc_self lowerLT_suc lowerLT_irrefl
  lowerLT_trans lowerLT_trichotomy lowerLT_iff_suc_le lowerLE_add_right lowerLE_mul_right
end Classicism.MathematicalContingency
