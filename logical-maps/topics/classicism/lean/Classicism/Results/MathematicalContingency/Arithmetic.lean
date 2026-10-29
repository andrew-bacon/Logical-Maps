import Classicism.Results.MathematicalContingency.ModalLemmas
/-! Impredicative arithmetic, reconstructed by OpenAI Codex, prompted by Andrew Bacon. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]
theorem lowerNat_zero : LowerNat (AtLeastZero σ) := fun _ h => h.1
theorem lowerNat_suc (n : (σ → Prop) → Prop) (h : LowerNat n) : LowerNat (SucCard n) :=
  fun Z hz => hz.2 n (h Z hz)
theorem lowerNat_induction (Z : ((σ → Prop) → Prop) → Prop)
    (hz : Z (AtLeastZero σ)) (hs : ∀ n, LowerNat n → Z n → Z (SucCard n))
    (n : (σ → Prop) → Prop) (hn : LowerNat n) : Z n :=
  (hn (fun n => LowerNat n ∧ Z n)
    ⟨⟨lowerNat_zero, hz⟩, fun n h => ⟨lowerNat_suc n h.1, hs n h.1 h.2⟩⟩).2
theorem lowerNat_cases (n : (σ → Prop) → Prop) (hn : LowerNat n) :
    n = AtLeastZero σ ∨ ∃ m, LowerNat m ∧ n = SucCard m :=
  lowerNat_induction (fun n => n = AtLeastZero σ ∨ ∃ m, LowerNat m ∧ n = SucCard m) (Or.inl rfl) (fun m hm _ => Or.inr ⟨m, hm, rfl⟩) n hn
theorem lowerPeano_of_box (h : DraftBoxInfinity σ) : LowerPeano σ := box_elim h
theorem lowerNat_suc_ne_zero (h : LowerPeano σ) (n : (σ → Prop) → Prop)
    (hn : LowerNat n) : SucCard n ≠ AtLeastZero σ := fun he => h.1 n hn he.symm
theorem lowerNat_suc_injective (h : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hm : LowerNat m) (hn : LowerNat n) (he : SucCard m = SucCard n) : m = n := h.2 m n hm hn he

def LowerSum (m n k : (σ → Prop) → Prop) : Prop :=
  ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop, R (AtLeastZero σ) m →
    (∀ a b, LowerNat a → LowerNat b → R a b → R (SucCard a) (SucCard b)) → R n k

theorem lowerSum_zero (m : (σ → Prop) → Prop) : LowerSum m (AtLeastZero σ) m := fun _ hz _ => hz
theorem lowerSum_suc (m n k : (σ → Prop) → Prop) (hn : LowerNat n) (hk : LowerNat k)
    (h : LowerSum m n k) : LowerSum m (SucCard n) (SucCard k) :=
  fun R hz hs => hs n k hn hk (h R hz hs)
theorem lowerSum_numbers (m n k : (σ → Prop) → Prop) (hm : LowerNat m)
    (h : LowerSum m n k) : LowerNat n ∧ LowerNat k :=
  h (fun a b => LowerNat a ∧ LowerNat b) ⟨lowerNat_zero, hm⟩
    (fun a b ha hb _ => ⟨lowerNat_suc a ha, lowerNat_suc b hb⟩)
theorem lowerSum_total (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n) :
    ∃ k, LowerNat k ∧ LowerSum m n k :=
  lowerNat_induction (fun n => ∃ k, LowerNat k ∧ LowerSum m n k) ⟨m, hm, lowerSum_zero m⟩
    (fun a ha ih => ih.elim fun b hb => ⟨SucCard b, lowerNat_suc b hb.1,
      lowerSum_suc m a b ha hb.1 hb.2⟩) n hn

theorem lowerSum_cases (m n k : (σ → Prop) → Prop) (h : LowerSum m n k) :
    (n = AtLeastZero σ ∧ k = m) ∨
    ∃ a b, LowerNat a ∧ LowerNat b ∧ LowerSum m a b ∧ n = SucCard a ∧ k = SucCard b := by
  have hh := h (fun a b => LowerSum m a b ∧ ((a = AtLeastZero σ ∧ b = m) ∨
    ∃ c d, LowerNat c ∧ LowerNat d ∧ LowerSum m c d ∧ a = SucCard c ∧ b = SucCard d))
    ⟨lowerSum_zero m, Or.inl ⟨rfl, rfl⟩⟩
    (fun a b ha hb ih => ⟨lowerSum_suc m a b ha hb ih.1, Or.inr ⟨a,b,ha,hb,ih.1,rfl,rfl⟩⟩)
  exact hh.2

theorem lowerSum_functional (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hn : LowerNat n) : ∀ k l, LowerSum m n k → LowerSum m n l → k = l := by
  apply lowerNat_induction _ ?_ ?_ n hn
  · intro k l hk hl
    have hk0 : k = m := (lowerSum_cases m _ k hk).elim And.right
      (fun h => h.elim fun a ha => ha.elim fun b hb => (hp.1 a hb.1 hb.2.2.2.1).elim)
    have hl0 : l = m := (lowerSum_cases m _ l hl).elim And.right
      (fun h => h.elim fun a ha => ha.elim fun b hb => (hp.1 a hb.1 hb.2.2.2.1).elim)
    exact hk0.trans hl0.symm
  · intro a ha ih k l hk hl
    obtain hk0 | ⟨b,c,hb,hc,hbc,he,hk'⟩ := lowerSum_cases m _ k hk
    · exact (lowerNat_suc_ne_zero hp a ha hk0.1).elim
    obtain hl0 | ⟨d,f,hd,hf,hdf,he',hl'⟩ := lowerSum_cases m _ l hl
    · exact (lowerNat_suc_ne_zero hp a ha hl0.1).elim
    have hab := hp.2 a b ha hb he
    have had := hp.2 a d ha hd he'
    subst b; subst d
    exact hk'.trans ((congrArg SucCard (ih c f hbc hdf)).trans hl'.symm)

def LowerProd (m n k : (σ → Prop) → Prop) : Prop :=
  ∀ R : ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop, R (AtLeastZero σ) (AtLeastZero σ) →
    (∀ a b c, LowerNat a → LowerNat b → LowerNat c → R a b → LowerSum m b c → R (SucCard a) c) → R n k

theorem lowerProd_zero (m : (σ → Prop) → Prop) : LowerProd m (AtLeastZero σ) (AtLeastZero σ) := fun _ hz _ => hz
theorem lowerProd_suc (m a b c : (σ → Prop) → Prop)
    (ha : LowerNat a) (hb : LowerNat b) (hc : LowerNat c)
    (h : LowerProd m a b) (hs : LowerSum m b c) : LowerProd m (SucCard a) c :=
  fun R hz step => step a b c ha hb hc (h R hz step) hs

theorem lowerProd_numbers (m n k : (σ → Prop) → Prop) (h : LowerProd m n k) :
    LowerNat n ∧ LowerNat k := h (fun a b => LowerNat a ∧ LowerNat b)
      ⟨lowerNat_zero,lowerNat_zero⟩ (fun a _ c ha _ hc _ _ => ⟨lowerNat_suc a ha,hc⟩)
theorem lowerProd_total (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n) :
    ∃ k, LowerNat k ∧ LowerProd m n k := by
  apply lowerNat_induction _ ⟨AtLeastZero σ, lowerNat_zero, lowerProd_zero m⟩ ?_ n hn
  intro a ha ih
  obtain ⟨b,hb,hp⟩ := ih
  obtain ⟨c,hc,hs⟩ := lowerSum_total m b hm hb
  exact ⟨c,hc,lowerProd_suc m a b c ha hb hc hp hs⟩

theorem lowerProd_cases (m n k : (σ → Prop) → Prop) (h : LowerProd m n k) :
    (n = AtLeastZero σ ∧ k = AtLeastZero σ) ∨
    ∃ a b c, LowerNat a ∧ LowerNat b ∧ LowerNat c ∧ LowerProd m a b ∧
      LowerSum m b c ∧ n = SucCard a ∧ k = c := by
  exact (h (fun a b => LowerProd m a b ∧ ((a = AtLeastZero σ ∧ b = AtLeastZero σ) ∨
    ∃ c d f, LowerNat c ∧ LowerNat d ∧ LowerNat f ∧ LowerProd m c d ∧
      LowerSum m d f ∧ a = SucCard c ∧ b = f))
    ⟨lowerProd_zero m,Or.inl ⟨rfl,rfl⟩⟩
    (fun a b c ha hb hc ih hs => ⟨lowerProd_suc m a b c ha hb hc ih.1 hs,
      Or.inr ⟨a,b,c,ha,hb,hc,ih.1,hs,rfl,rfl⟩⟩)).2

theorem lowerProd_functional (hp : LowerPeano σ) (m n : (σ → Prop) → Prop)
    (hn : LowerNat n) : ∀ k l, LowerProd m n k → LowerProd m n l → k = l := by
  apply lowerNat_induction _ ?_ ?_ n hn
  · intro k l hk hl
    have hz : ∀ k, LowerProd m (AtLeastZero σ) k → k = AtLeastZero σ := by
      intro k hk
      obtain h0 | ⟨a,b,c,ha,hb,hc,hp',hs,he,hk'⟩ := lowerProd_cases m _ k hk
      · exact h0.2
      · exact (hp.1 a ha he).elim
    exact (hz k hk).trans (hz l hl).symm
  · intro a ha ih k l hk hl
    obtain h0 | ⟨b,c,d,hb,hc,hd,hbc,hcd,he,hk'⟩ := lowerProd_cases m _ k hk
    · exact (lowerNat_suc_ne_zero hp a ha h0.1).elim
    obtain h0 | ⟨f,g,j,hf,hg,hj,hfg,hgj,he',hl'⟩ := lowerProd_cases m _ l hl
    · exact (lowerNat_suc_ne_zero hp a ha h0.1).elim
    have hab := hp.2 a b ha hb he
    have haf := hp.2 a f ha hf he'
    subst b; subst f
    have hcg := ih c g hbc hfg
    subst g
    exact hk'.trans ((lowerSum_functional hp m c hc d j hcd hgj).trans hl'.symm)

#classicism_check lowerNat_zero lowerNat_suc lowerNat_induction lowerNat_cases lowerPeano_of_box
  lowerNat_suc_ne_zero lowerNat_suc_injective lowerSum_zero lowerSum_suc lowerSum_numbers
  lowerSum_total lowerSum_cases lowerSum_functional lowerProd_zero lowerProd_suc lowerProd_numbers
  lowerProd_total lowerProd_cases lowerProd_functional
#classicism_types lowerNat_zero lowerNat_suc lowerNat_induction lowerNat_cases lowerPeano_of_box
  lowerNat_suc_ne_zero lowerNat_suc_injective lowerSum_zero lowerSum_suc lowerSum_numbers
  lowerSum_total lowerSum_cases lowerSum_functional lowerProd_zero lowerProd_suc lowerProd_numbers
  lowerProd_total lowerProd_cases lowerProd_functional
end Classicism.MathematicalContingency
