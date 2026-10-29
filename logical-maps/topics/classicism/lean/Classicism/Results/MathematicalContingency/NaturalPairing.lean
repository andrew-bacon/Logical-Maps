import Classicism.Results.MathematicalContingency.NaturalOrder

/-! A polynomial injection of ordered pairs of LowerNat into LowerNat.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
The graph represents (m+n)^2+m; no choice of a function or ambient Lean Nat is used.
This is an injection, not a claim that every natural is a pair code. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem lowerLT_of_le_of_lt (hp : LowerPeano σ) (a b c : (σ → Prop) → Prop)
    (hab : LowerLE a b) (hbc : LowerLT b c) : LowerLT a c := by
  refine ⟨lowerLE_trans a b c hab hbc.1,?_⟩
  intro e
  subst c
  exact hbc.2 (lowerLE_antisymm hp b a hbc.1 hab)

theorem lowerLT_of_lt_of_le (hp : LowerPeano σ) (a b c : (σ → Prop) → Prop)
    (hab : LowerLT a b) (hbc : LowerLE b c) : LowerLT a c := by
  refine ⟨lowerLE_trans a b c hab.1 hbc,?_⟩
  intro e
  subst c
  exact hab.2 (lowerLE_antisymm hp a b hab.1 hbc)

theorem lowerLE_square (hp : LowerPeano σ) (a b p q : (σ → Prop) → Prop)
    (hab : LowerLE a b) (ha : LowerProd a a p) (hb : LowerProd b b q) : LowerLE p q := by
  obtain ⟨r,hr,hba⟩ := lowerProd_total b a hab.2.1 hab.1
  have hpr := lowerLE_mul_right hp a b a p r hab.1 hab ha hba
  have hrq := lowerLE_mul_right hp a b b r q hab.2.1 hab
    (lowerProd_comm hp b a r hab.2.1 hba) hb
  exact lowerLE_trans p r q hpr hrq

theorem lowerLT_sum_positive (hp : LowerPeano σ) (a b c : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hb0 : b ≠ AtLeastZero σ)
    (hs : LowerSum a b c) : LowerLT a c := by
  refine ⟨⟨ha,(lowerSum_numbers a b c ha hs).2,b,hb,hs⟩,?_⟩
  intro e
  subst c
  exact hb0 ((lowerSum_self_iff hp a b ha hb).mp hs)

/-- The interval ending at s*s+s lies strictly below (s+1)*(s+1). -/
theorem lowerSquare_gap (hp : LowerPeano σ) (s p d : (σ → Prop) → Prop)
    (hs : LowerNat s) (hsp : LowerProd s s p) (hpd : LowerSum p s d) :
    ∃ q, LowerNat q ∧ LowerProd (SucCard s) (SucCard s) q ∧ LowerLT d q := by
  have hpN := (lowerProd_numbers s s p hsp).2
  have hd := (lowerSum_numbers p s d hpN hpd).2
  have hss := lowerNat_suc s hs
  obtain ⟨q,hq,hsd⟩ := lowerSum_total (SucCard s) d hss hd
  have hprod := lowerProd_suc s s p d hs hpN hd hsp (lowerSum_comm p s d hpN hpd)
  have hprod' := lowerProd_comm hp s (SucCard s) d hs hprod
  exact ⟨q,hq,lowerProd_suc (SucCard s) s d q hs hd hq hprod' hsd,
    lowerLT_sum_positive hp d (SucCard s) q hd hss (lowerNat_suc_ne_zero hp s hs)
      (lowerSum_comm (SucCard s) d q hss hsd)⟩

def LowerPair (m n k : (σ → Prop) → Prop) : Prop :=
  LowerNat m ∧ LowerNat n ∧ ∃ s p, LowerNat s ∧ LowerNat p ∧
    LowerSum m n s ∧ LowerProd s s p ∧ LowerSum p m k

theorem lowerPair_numbers (m n k : (σ → Prop) → Prop) (h : LowerPair m n k) :
    LowerNat m ∧ LowerNat n ∧ LowerNat k := by
  obtain ⟨hm,hn,s,p,hs,hp,hms,hsp,hpm⟩ := h
  exact ⟨hm,hn,(lowerSum_numbers p m k hp hpm).2⟩

theorem lowerPair_total (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n) :
    ∃ k, LowerNat k ∧ LowerPair m n k := by
  obtain ⟨s,hs,hms⟩ := lowerSum_total m n hm hn
  obtain ⟨p,hp,hsp⟩ := lowerProd_total s s hs hs
  obtain ⟨k,hk,hpm⟩ := lowerSum_total p m hp hm
  exact ⟨k,hk,hm,hn,s,p,hs,hp,hms,hsp,hpm⟩

theorem lowerPair_functional (hp : LowerPeano σ) (m n k l : (σ → Prop) → Prop)
    (hk : LowerPair m n k) (hl : LowerPair m n l) : k = l := by
  obtain ⟨hm,hn,s,p,hs,hpN,hms,hsp,hpm⟩ := hk
  obtain ⟨_,_,t,q,ht,hq,hmt,htq,hqm⟩ := hl
  have e := lowerSum_functional hp m n hn s t hms hmt
  subst t
  have e := lowerProd_functional hp s s hs p q hsp htq
  subst q
  exact lowerSum_functional hp p m hm k l hpm hqm

/-- Codes on strictly later diagonals are strictly larger. -/
theorem lowerPair_diagonal_order (hp : LowerPeano σ)
    (m a s t p q k l : (σ → Prop) → Prop)
    (ha : LowerNat a) (hs : LowerNat s) (ht : LowerNat t)
    (hms : LowerLE m s) (hst : LowerLT s t)
    (hsp : LowerProd s s p) (htq : LowerProd t t q)
    (hpm : LowerSum p m k) (hqa : LowerSum q a l) : LowerLT k l := by
  have hpN := (lowerProd_numbers s s p hsp).2
  have hqN := (lowerProd_numbers t t q htq).2
  obtain ⟨d,hd,hpd⟩ := lowerSum_total p s hpN hs
  have hkd := lowerLE_add_right hp m s p k d hpN hms
    (lowerSum_comm p m k hpN hpm) (lowerSum_comm p s d hpN hpd)
  obtain ⟨r,hr,hssr,hdr⟩ := lowerSquare_gap hp s p d hs hsp hpd
  have hrq := lowerLE_square hp (SucCard s) t r q
    ((lowerLT_iff_suc_le hp s t hs ht).mp hst) hssr htq
  have hql : LowerLE q l := ⟨hqN,(lowerSum_numbers q a l hqN hqa).2,a,ha,hqa⟩
  exact lowerLT_of_lt_of_le hp k r l (lowerLT_of_le_of_lt hp k d r hkd hdr)
    (lowerLE_trans r q l hrq hql)

theorem lowerPair_injective (hp : LowerPeano σ) (m n a b k : (σ → Prop) → Prop)
    (h1 : LowerPair m n k) (h2 : LowerPair a b k) : m = a ∧ n = b := by
  obtain ⟨hm,hn,s,p,hs,hpN,hms,hsp,hpm⟩ := h1
  obtain ⟨ha,hb,t,q,ht,hqN,hat,htq,hqa⟩ := h2
  have hmsLE : LowerLE m s := ⟨hm,hs,n,hn,hms⟩
  have hatLE : LowerLE a t := ⟨ha,ht,b,hb,hat⟩
  have est : s = t := by
    obtain hst | e | hts := lowerLT_trichotomy s t hs ht
    · exact (lowerLT_irrefl k (lowerPair_diagonal_order hp m a s t p q k k
        ha hs ht hmsLE hst hsp htq hpm hqa)).elim
    · exact e
    · exact (lowerLT_irrefl k (lowerPair_diagonal_order hp a m t s q p k k
        hm ht hs hatLE hts htq hsp hqa hpm)).elim
  subst t
  have e := lowerProd_functional hp s s hs p q hsp htq
  subst q
  have ema := lowerSum_cancel_left hp p m a k hpN hm ha hpm hqa
  subst a
  exact ⟨rfl,lowerSum_cancel_left hp m n b s hm hn hb hms hat⟩

theorem lowerPair_zero : LowerPair (AtLeastZero σ) (AtLeastZero σ) (AtLeastZero σ) :=
  ⟨lowerNat_zero,lowerNat_zero,AtLeastZero σ,AtLeastZero σ,lowerNat_zero,lowerNat_zero,
    lowerSum_zero _,lowerProd_zero _,lowerSum_zero _⟩

theorem lowerPair_zero_iff (hp : LowerPeano σ) (m n : (σ → Prop) → Prop) :
    LowerPair m n (AtLeastZero σ) ↔ m = AtLeastZero σ ∧ n = AtLeastZero σ := by
  constructor
  · intro h
    exact lowerPair_injective hp m n _ _ _ h lowerPair_zero
  · intro ⟨hm,hn⟩
    subst m; subst n
    exact lowerPair_zero

#classicism_check lowerLT_of_le_of_lt lowerLT_of_lt_of_le lowerLE_square lowerLT_sum_positive
  lowerSquare_gap lowerPair_numbers lowerPair_total lowerPair_functional lowerPair_diagonal_order
  lowerPair_injective lowerPair_zero lowerPair_zero_iff
#classicism_types lowerLT_of_le_of_lt lowerLT_of_lt_of_le lowerLE_square lowerLT_sum_positive
  lowerSquare_gap lowerPair_numbers lowerPair_total lowerPair_functional lowerPair_diagonal_order
  lowerPair_injective lowerPair_zero lowerPair_zero_iff
end Classicism.MathematicalContingency
