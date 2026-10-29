import Classicism.Results.MathematicalContingency.Addition

/-! Relational multiplication algebra for the paper's at-least naturals.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
No identification with upstream exact-cardinality naturals is made. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

/-- The reverse associativity diagram, constructed without choosing an operation. -/
theorem lowerSum_assoc_left (a b c w v : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hc : LowerNat c)
    (hbc : LowerSum b c w) (haw : LowerSum a w v) :
    ∃ u, LowerNat u ∧ LowerSum a b u ∧ LowerSum u c v := by
  obtain ⟨x,hx,hca,hbx⟩ := lowerSum_assoc b c w a v hc hbc (lowerSum_comm a w v ha haw)
  obtain ⟨u,hu,hab,hcu⟩ := lowerSum_assoc c a x b v ha hca (lowerSum_comm b x v hb hbx)
  exact ⟨u,hu,hab,lowerSum_comm c u v hc hcu⟩

theorem lowerSum_left_comm (a b c u v : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hc : LowerNat c)
    (hbc : LowerSum b c u) (hau : LowerSum a u v) :
    ∃ w, LowerNat w ∧ LowerSum a c w ∧ LowerSum b w v := by
  obtain ⟨x,hx,hab,hxc⟩ := lowerSum_assoc_left a b c u v ha hb hc hbc hau
  exact lowerSum_assoc b a x c v ha (lowerSum_comm a b x ha hab) hxc

theorem lowerProd_induction (m : (σ → Prop) → Prop)
    (P : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)
    (hz : P (AtLeastZero σ) (AtLeastZero σ))
    (step : ∀ a b c, LowerNat a → LowerNat b → LowerNat c →
      LowerProd m a b → P a b → LowerSum m b c → P (SucCard a) c)
    (n k : (σ → Prop) → Prop) (h : LowerProd m n k) : P n k :=
  (h (fun a b => LowerProd m a b ∧ P a b) ⟨lowerProd_zero m,hz⟩
    (fun a b c ha hb hc ih hs =>
      ⟨lowerProd_suc m a b c ha hb hc ih.1 hs,step a b c ha hb hc ih.1 ih.2 hs⟩)).2

theorem lowerProd_zero_left (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    LowerProd (AtLeastZero σ) n (AtLeastZero σ) :=
  lowerNat_induction (fun n => LowerProd (AtLeastZero σ) n (AtLeastZero σ))
    (lowerProd_zero _) (fun a ha ih => lowerProd_suc _ a _ _ ha lowerNat_zero lowerNat_zero
      ih (lowerSum_zero _)) n hn

theorem lowerProd_zero_iff (hp : LowerPeano σ) (m k : (σ → Prop) → Prop) :
    LowerProd m (AtLeastZero σ) k ↔ k = AtLeastZero σ :=
  ⟨fun h => lowerProd_functional hp m _ lowerNat_zero k _ h (lowerProd_zero m),
    fun h => h.symm ▸ lowerProd_zero m⟩

theorem lowerProd_suc_iff (hp : LowerPeano σ) (m n k : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) :
    LowerProd m (SucCard n) k ↔ ∃ b, LowerNat b ∧ LowerProd m n b ∧ LowerSum m b k := by
  constructor
  · intro h
    obtain hz | ⟨a,b,c,ha,hb,hc,hab,hs,he,hk⟩ := lowerProd_cases m _ k h
    · exact (lowerNat_suc_ne_zero hp n hn hz.1).elim
    · have e := hp.2 n a hn ha he
      subst a; subst c
      exact ⟨b,hb,hab,hs⟩
  · intro ⟨b,hb,hab,hs⟩
    exact lowerProd_suc m n b k hn hb (lowerSum_numbers m b k hm hs).2 hab hs

/-- (m+1)n = mn+n, with both operations represented by graphs. -/
theorem lowerProd_suc_left (hp : LowerPeano σ) (m n k l : (σ → Prop) → Prop)
    (hm : LowerNat m) (h : LowerProd m n k) (hs : LowerSum n k l) :
    LowerProd (SucCard m) n l := by
  have main : ∀ (n k : (σ → Prop) → Prop), LowerProd m n k →
      ∀ l, LowerSum n k l → LowerProd (SucCard m) n l := by
    intro n k h
    apply lowerProd_induction m (fun n k => ∀ l, LowerSum n k l → LowerProd (SucCard m) n l) ?_ ?_ n k h
    · intro l hs
      have e := (lowerSum_zero_iff hp (AtLeastZero σ) l).mp hs
      exact e.symm ▸ lowerProd_zero (SucCard m)
    · intro a b c ha hb hc _ ih hmb l hsl
      obtain ⟨d,hd,had⟩ := lowerSum_total a b ha hb
      obtain ⟨t,ht,hmd⟩ := lowerSum_total m d hm hd
      obtain ⟨w,hw,hmw,haw⟩ := lowerSum_left_comm m a b d t hm ha hb had hmd
      have e := lowerSum_functional hp m b hb w c hmw hmb
      subst w
      have el := lowerSum_functional hp (SucCard a) c hc l (SucCard t) hsl
        (lowerSum_suc_left a c t haw)
      exact el.symm ▸ lowerProd_suc (SucCard m) a d (SucCard t) ha hd
        (lowerNat_suc t ht) (ih d had) (lowerSum_suc_left m d t hmd)
  exact main n k h l hs

theorem lowerProd_comm (hp : LowerPeano σ) (m n k : (σ → Prop) → Prop)
    (hm : LowerNat m) (h : LowerProd m n k) : LowerProd n m k :=
  lowerProd_induction m (fun n k => LowerProd n m k) (lowerProd_zero_left m hm)
    (fun a b c ha _ _ _ ih hs => lowerProd_suc_left hp a m b c ha ih hs) n k h

theorem lowerProd_comm_iff (hp : LowerPeano σ) (m n k : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) : LowerProd m n k ↔ LowerProd n m k :=
  ⟨lowerProd_comm hp m n k hm,lowerProd_comm hp n m k hn⟩

theorem lowerProd_one_right (m : (σ → Prop) → Prop) (hm : LowerNat m) :
    LowerProd m (SucCard (AtLeastZero σ)) m :=
  lowerProd_suc m _ _ m lowerNat_zero lowerNat_zero hm (lowerProd_zero m) (lowerSum_zero m)

theorem lowerProd_one_left (hp : LowerPeano σ) (m : (σ → Prop) → Prop)
    (hm : LowerNat m) : LowerProd (SucCard (AtLeastZero σ)) m m :=
  lowerProd_comm hp m _ m hm (lowerProd_one_right m hm)

/-- a(b+c)=ab+ac: every compatible addition/product diagram commutes. -/
theorem lowerProd_distrib_left (hp : LowerPeano σ)
    (a b c d u v w : (σ → Prop) → Prop) (ha : LowerNat a)
    (hbc : LowerSum b c d) (hab : LowerProd a b u)
    (hac : LowerProd a c v) (huv : LowerSum u v w) : LowerProd a d w := by
  have hu := (lowerProd_numbers a b u hab).2
  have main : ∀ (c d : (σ → Prop) → Prop), LowerSum b c d →
      ∀ v w, LowerProd a c v → LowerSum u v w → LowerProd a d w := by
    intro c d hbc
    apply lowerSum_induction b (fun c d => ∀ v w, LowerProd a c v → LowerSum u v w → LowerProd a d w) ?_ ?_ c d hbc
    · intro v w hav huw
      have e := (lowerProd_zero_iff hp a v).mp hav
      subst v
      have e := (lowerSum_zero_iff hp u w).mp huw
      exact e.symm ▸ hab
    · intro n k hn hk _ ih v w hav huw
      obtain ⟨t,ht,hat,hatv⟩ := (lowerProd_suc_iff hp a n v ha hn).mp hav
      obtain ⟨y,hy,huty,hayw⟩ := lowerSum_left_comm u a t v w hu ha ht hatv huw
      exact lowerProd_suc a k y w hk hy (lowerSum_numbers u v w hu huw).2
        (ih t y hat huty) hayw
  exact main c d hbc v w hac huv

theorem lowerProd_distrib_right (hp : LowerPeano σ)
    (a b c d u v w : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hc : LowerNat c)
    (hab : LowerSum a b d) (hac : LowerProd a c u)
    (hbc : LowerProd b c v) (huv : LowerSum u v w) : LowerProd d c w := by
  have h := lowerProd_distrib_left hp c a b d u v w hc hab
    (lowerProd_comm hp a c u ha hac) (lowerProd_comm hp b c v hb hbc) huv
  exact lowerProd_comm hp c d w hc h

/-- (ab)c=a(bc), as equality of relational computation results. -/
theorem lowerProd_assoc (hp : LowerPeano σ)
    (a b c u v w : (σ → Prop) → Prop) (ha : LowerNat a)
    (hab : LowerProd a b u) (hbc : LowerProd b c v) (huc : LowerProd u c w) :
    LowerProd a v w := by
  have hu := (lowerProd_numbers a b u hab).2
  have main : ∀ (c v : (σ → Prop) → Prop), LowerProd b c v →
      ∀ w, LowerProd u c w → LowerProd a v w := by
    intro c v hbc
    apply lowerProd_induction b (fun c v => ∀ w, LowerProd u c w → LowerProd a v w) ?_ ?_ c v hbc
    · intro w huw
      exact ((lowerProd_zero_iff hp u w).mp huw).symm ▸ lowerProd_zero a
    · intro n k l hn hk hl _ ih hbk w huw
      obtain ⟨t,ht,hut,hus⟩ := (lowerProd_suc_iff hp u n w hu hn).mp huw
      exact lowerProd_distrib_left hp a b k l u t w ha hbk hab (ih t hut) hus
  exact main c v hbc w huc

/-- No nontrivial sum is zero, using only the explicit Peano laws. -/
theorem lowerSum_eq_zero (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (h : LowerSum m n (AtLeastZero σ)) : m = AtLeastZero σ ∧ n = AtLeastZero σ := by
  obtain hz | ⟨a,b,ha,hb,hs,he,hk⟩ := lowerSum_cases m n _ h
  · exact ⟨hz.2.symm,hz.1⟩
  · exact (hp.1 b hb hk).elim

theorem lowerSum_self_iff (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) : LowerSum m n m ↔ n = AtLeastZero σ :=
  ⟨fun h => lowerSum_cancel_left hp m n _ m hm hn lowerNat_zero h (lowerSum_zero m),
    fun h => h.symm ▸ lowerSum_zero m⟩

theorem lowerProd_eq_zero (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (h : LowerProd m n (AtLeastZero σ)) : m = AtLeastZero σ ∨ n = AtLeastZero σ := by
  obtain hz | ⟨a,b,c,ha,hb,hc,hab,hs,he,hk⟩ := lowerProd_cases m n _ h
  · exact Or.inr hz.1
  · subst c
    exact Or.inl (lowerSum_eq_zero hp m b hs).1

theorem lowerProd_eq_zero_iff (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hn : LowerNat n) : LowerProd m n (AtLeastZero σ) ↔ m = AtLeastZero σ ∨ n = AtLeastZero σ :=
  ⟨lowerProd_eq_zero hp m n,fun h => h.elim
    (fun hm => hm.symm ▸ lowerProd_zero_left n hn) (fun hn => hn.symm ▸ lowerProd_zero m)⟩

theorem lowerProd_ne_zero (hp : LowerPeano σ) (m n k : (σ → Prop) → Prop)
    (hm : m ≠ AtLeastZero σ) (hn : n ≠ AtLeastZero σ) (h : LowerProd m n k) :
    k ≠ AtLeastZero σ :=
  fun hk => (lowerProd_eq_zero hp m n (hk ▸ h)).elim hm hn

theorem lowerProd_cancel_left (hp : LowerPeano σ) (a b c k : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hc : LowerNat c) (ha0 : a ≠ AtLeastZero σ)
    (hab : LowerProd a b k) (hac : LowerProd a c k) : b = c := by
  have main : ∀ (b : (σ → Prop) → Prop), LowerNat b → ∀ c k, LowerNat c →
      LowerProd a b k → LowerProd a c k → b = c := by
    intro b hb
    apply lowerNat_induction _ ?_ ?_ b hb
    · intro c k hc h0 hck
      have e := (lowerProd_zero_iff hp a k).mp h0
      subst k
      exact (lowerProd_eq_zero hp a c hck).elim (fun he => (ha0 he).elim) Eq.symm
    · intro b hb ih c k hc hbk hck
      obtain he | ⟨d,hd,he⟩ := lowerNat_cases c hc
      · subst c
        have e := (lowerProd_zero_iff hp a k).mp hck
        exact (lowerProd_ne_zero hp a (SucCard b) k ha0
          (lowerNat_suc_ne_zero hp b hb) hbk e).elim
      · subst c
        obtain ⟨u,hu,hbu,hsu⟩ := (lowerProd_suc_iff hp a b k ha hb).mp hbk
        obtain ⟨v,hv,hdv,hsv⟩ := (lowerProd_suc_iff hp a d k ha hd).mp hck
        have e := lowerSum_cancel_left hp a u v k ha hu hv hsu hsv
        subst v
        exact congrArg SucCard (ih d u hd hbu hdv)
  exact main b hb c k hc hab hac

theorem lowerProd_cancel_right (hp : LowerPeano σ) (a b c k : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hc : LowerNat c) (ha0 : a ≠ AtLeastZero σ)
    (hba : LowerProd b a k) (hca : LowerProd c a k) : b = c :=
  lowerProd_cancel_left hp a b c k ha hb hc ha0
    (lowerProd_comm hp b a k hb hba) (lowerProd_comm hp c a k hc hca)

#classicism_check lowerSum_assoc_left lowerSum_left_comm lowerProd_induction lowerProd_zero_left
  lowerProd_zero_iff lowerProd_suc_iff lowerProd_suc_left lowerProd_comm lowerProd_comm_iff
  lowerProd_one_right lowerProd_one_left lowerProd_distrib_left lowerProd_distrib_right
  lowerProd_assoc lowerSum_eq_zero lowerSum_self_iff lowerProd_eq_zero lowerProd_eq_zero_iff
  lowerProd_ne_zero lowerProd_cancel_left lowerProd_cancel_right
#classicism_types lowerSum_assoc_left lowerSum_left_comm lowerProd_induction lowerProd_zero_left
  lowerProd_zero_iff lowerProd_suc_iff lowerProd_suc_left lowerProd_comm lowerProd_comm_iff
  lowerProd_one_right lowerProd_one_left lowerProd_distrib_left lowerProd_distrib_right
  lowerProd_assoc lowerSum_eq_zero lowerSum_self_iff lowerProd_eq_zero lowerProd_eq_zero_iff
  lowerProd_ne_zero lowerProd_cancel_left lowerProd_cancel_right
end Classicism.MathematicalContingency
