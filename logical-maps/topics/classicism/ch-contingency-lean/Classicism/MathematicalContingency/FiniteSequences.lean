import Classicism.MathematicalContingency.NaturalPairing

/-! Finite sequence graphs over an arbitrary carrier, indexed by LowerNat.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
Graphs are compared by current coextension, not unrestricted extensional identity. -/
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]

def SeqEmpty (F : ((σ → Prop) → Prop) → τ → Prop) : Prop := ∀ i x, ¬ F i x

def SeqCons (x : τ) (F G : ((σ → Prop) → Prop) → τ → Prop) : Prop :=
  ∀ i y, G i y ↔ (i = AtLeastZero σ ∧ y = x) ∨ ∃ j, LowerNat j ∧ i = SucCard j ∧ F j y

def FiniteSeq (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) : Prop :=
  ∀ P : ((σ → Prop) → Prop) → (((σ → Prop) → Prop) → τ → Prop) → Prop,
    (∀ F, SeqEmpty F → P (AtLeastZero σ) F) →
    (∀ n F x G, LowerNat n → A x → SeqCons x F G → P n F → P (SucCard n) G) → P n F

theorem seqEmpty_exists : ∃ F : ((σ → Prop) → Prop) → τ → Prop, SeqEmpty F :=
  ⟨fun _ _ => False,fun _ _ h => h⟩

theorem seqCons_exists (x : τ) (F : ((σ → Prop) → Prop) → τ → Prop) : ∃ G, SeqCons x F G :=
  ⟨fun i y => (i = AtLeastZero σ ∧ y = x) ∨ ∃ j, LowerNat j ∧ i = SucCard j ∧ F j y,
    fun _ _ => Iff.rfl⟩

theorem seqCons_head (hp : LowerPeano σ) (x y : τ)
    (F G : ((σ → Prop) → Prop) → τ → Prop) (h : SeqCons x F G) :
    G (AtLeastZero σ) y ↔ y = x := by
  constructor
  · intro hy
    obtain hz | ⟨j,hj,e,_⟩ := (h _ y).mp hy
    · exact hz.2
    · exact (hp.1 j hj e).elim
  · intro e
    exact (h _ y).mpr (Or.inl ⟨rfl,e⟩)

theorem seqCons_tail (hp : LowerPeano σ) (x y : τ)
    (F G : ((σ → Prop) → Prop) → τ → Prop) (h : SeqCons x F G)
    (i : (σ → Prop) → Prop) (hi : LowerNat i) : G (SucCard i) y ↔ F i y := by
  constructor
  · intro hy
    obtain hz | ⟨j,hj,e,hjF⟩ := (h _ y).mp hy
    · exact (lowerNat_suc_ne_zero hp i hi hz.1).elim
    · have e := hp.2 i j hi hj e
      exact e.symm ▸ hjF
  · intro hy
    exact (h _ y).mpr (Or.inr ⟨i,hi,rfl,hy⟩)

theorem seqCons_not_empty (x : τ) (F G : ((σ → Prop) → Prop) → τ → Prop)
    (h : SeqCons x F G) : ¬ SeqEmpty G :=
  fun he => he _ x ((h _ x).mpr (Or.inl ⟨rfl,rfl⟩))

theorem seqCons_coext (x : τ) (F H G K : ((σ → Prop) → Prop) → τ → Prop)
    (h : SeqCons x F G) (k : SeqCons x H K) (e : ∀ i y, F i y ↔ H i y) :
    ∀ i y, G i y ↔ K i y := by
  intro i y
  constructor
  · intro hg
    apply (k i y).mpr
    obtain hz | ⟨j,hj,he,hf⟩ := (h i y).mp hg
    · exact Or.inl hz
    · exact Or.inr ⟨j,hj,he,(e j y).mp hf⟩
  · intro hk
    apply (h i y).mpr
    obtain hz | ⟨j,hj,he,hf⟩ := (k i y).mp hk
    · exact Or.inl hz
    · exact Or.inr ⟨j,hj,he,(e j y).mpr hf⟩

theorem finiteSeq_nil (A : τ → Prop) (F : ((σ → Prop) → Prop) → τ → Prop)
    (h : SeqEmpty F) : FiniteSeq A (AtLeastZero σ) F := fun _ hz _ => hz F h

theorem finiteSeq_cons (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F G : ((σ → Prop) → Prop) → τ → Prop) (x : τ)
    (hn : LowerNat n) (hx : A x) (hc : SeqCons x F G) (h : FiniteSeq A n F) :
    FiniteSeq A (SucCard n) G := fun P hz hs => hs n F x G hn hx hc (h P hz hs)

theorem finiteSeq_induction (A : τ → Prop)
    (P : ((σ → Prop) → Prop) → (((σ → Prop) → Prop) → τ → Prop) → Prop)
    (hz : ∀ F, SeqEmpty F → P (AtLeastZero σ) F)
    (step : ∀ n F x G, LowerNat n → A x → SeqCons x F G → FiniteSeq A n F → P n F → P (SucCard n) G)
    (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F) : P n F :=
  (h (fun n F => FiniteSeq A n F ∧ P n F) (fun F he => ⟨finiteSeq_nil A F he,hz F he⟩)
    (fun n F x G hn hx hc ih => ⟨finiteSeq_cons A n F G x hn hx hc ih.1,
      step n F x G hn hx hc ih.1 ih.2⟩)).2

theorem finiteSeq_length_nat (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F) : LowerNat n :=
  h (fun n _ => LowerNat n) (fun _ _ => lowerNat_zero)
    (fun n _ _ _ hn _ _ _ => lowerNat_suc n hn)

theorem finiteSeq_members (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F) :
    ∀ i x, F i x → LowerNat i ∧ A x := by
  apply h (fun _ F => ∀ i x, F i x → LowerNat i ∧ A x) ?_ ?_
  · intro F he i x hi
    exact (he i x hi).elim
  · intro n F x G hn hx hc ih i y hy
    obtain ⟨e,ey⟩ | ⟨j,hj,e,hf⟩ := (hc i y).mp hy
    · exact ⟨e.symm ▸ lowerNat_zero,ey.symm ▸ hx⟩
    · exact ⟨e.symm ▸ lowerNat_suc j hj,(ih j y hf).2⟩

theorem finiteSeq_cases (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F) :
    (n = AtLeastZero σ ∧ SeqEmpty F) ∨ ∃ m H x, LowerNat m ∧ A x ∧
      FiniteSeq A m H ∧ SeqCons x H F ∧ n = SucCard m :=
  finiteSeq_induction A (fun n F => (n = AtLeastZero σ ∧ SeqEmpty F) ∨
    ∃ m H x, LowerNat m ∧ A x ∧ FiniteSeq A m H ∧ SeqCons x H F ∧ n = SucCard m)
    (fun F he => Or.inl ⟨rfl,he⟩)
    (fun m H x G hm hx hc hs _ => Or.inr ⟨m,H,x,hm,hx,hs,hc,rfl⟩) n F h

theorem finiteSeq_zero_iff (hp : LowerPeano σ) (A : τ → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) : FiniteSeq A (AtLeastZero σ) F ↔ SeqEmpty F := by
  constructor
  · intro h
    obtain hz | ⟨m,H,x,hm,hx,hs,hc,e⟩ := finiteSeq_cases A _ F h
    · exact hz.2
    · exact (hp.1 m hm e).elim
  · exact finiteSeq_nil A F

theorem finiteSeq_functional (hp : LowerPeano σ) (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F) :
    ∀ i x y, F i x → F i y → x = y := by
  apply h (fun _ F => ∀ i x y, F i x → F i y → x = y) ?_ ?_
  · intro F he i x y hx _
    exact (he i x hx).elim
  · intro n F x G hn hx hc ih i y z hy hz
    obtain ⟨e,_⟩ | ⟨j,hj,e,_⟩ := (hc i y).mp hy
    · subst i
      exact ((seqCons_head hp x y F G hc).mp hy).trans ((seqCons_head hp x z F G hc).mp hz).symm
    · subst i
      exact ih j y z ((seqCons_tail hp x y F G hc j hj).mp hy)
        ((seqCons_tail hp x z F G hc j hj).mp hz)

theorem seqCons_injective (hp : LowerPeano σ) (x y : τ)
    (F H G K : ((σ → Prop) → Prop) → τ → Prop)
    (hf : ∀ i z, F i z → LowerNat i) (hh : ∀ i z, H i z → LowerNat i)
    (hc : SeqCons x F G) (hd : SeqCons y H K) (e : ∀ i z, G i z ↔ K i z) :
    x = y ∧ ∀ i z, F i z ↔ H i z := by
  refine ⟨(seqCons_head hp y x H K hd).mp ((e _ x).mp ((hc _ x).mpr (Or.inl ⟨rfl,rfl⟩))),?_⟩
  intro i z
  constructor
  · intro h
    exact (seqCons_tail hp y z H K hd i (hf i z h)).mp
      ((e _ z).mp ((seqCons_tail hp x z F G hc i (hf i z h)).mpr h))
  · intro h
    exact (seqCons_tail hp x z F G hc i (hh i z h)).mp
      ((e _ z).mpr ((seqCons_tail hp y z H K hd i (hh i z h)).mpr h))

theorem finiteSeq_coext (A : τ → Prop) (n : (σ → Prop) → Prop)
    (F G : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F)
    (e : ∀ i x, F i x ↔ G i x) : FiniteSeq A n G := by
  obtain ⟨he,hf⟩ | ⟨m,H,x,hm,hx,hs,hc,he⟩ := finiteSeq_cases A n F h
  · subst n
    exact finiteSeq_nil A G (fun i x hg => hf i x ((e i x).mpr hg))
  · subst n
    exact finiteSeq_cons A m H G x hm hx (fun i y => (e i y).symm.trans (hc i y)) hs

theorem finiteSeq_length_unique (hp : LowerPeano σ) (A : τ → Prop)
    (n m : (σ → Prop) → Prop) (F G : ((σ → Prop) → Prop) → τ → Prop)
    (h : FiniteSeq A n F) (k : FiniteSeq A m G) (e : ∀ i x, F i x ↔ G i x) : n = m := by
  have main : ∀ (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop),
      FiniteSeq A n F → ∀ m G, FiniteSeq A m G → (∀ i x, F i x ↔ G i x) → n = m := by
    intro n F h
    apply finiteSeq_induction A (fun n F => ∀ m G, FiniteSeq A m G →
      (∀ i x, F i x ↔ G i x) → n = m) ?_ ?_ n F h
    · intro F hf m G hg e
      obtain ⟨he,_⟩ | ⟨l,H,x,hl,hx,hs,hc,he⟩ := finiteSeq_cases A m G hg
      · exact he.symm
      · exact (hf _ x ((e _ x).mpr ((hc _ x).mpr (Or.inl ⟨rfl,rfl⟩)))).elim
    · intro n F x G hn hx hc hs ih m H hh e
      obtain ⟨he,hempty⟩ | ⟨l,J,y,hl,hy,hj,hd,he⟩ := finiteSeq_cases A m H hh
      · exact (hempty _ x ((e _ x).mp ((hc _ x).mpr (Or.inl ⟨rfl,rfl⟩)))).elim
      · have ht := (seqCons_injective hp x y F J G H
          (fun i z hf => (finiteSeq_members A n F hs i z hf).1)
          (fun i z hf => (finiteSeq_members A l J hj i z hf).1) hc hd e).2
        exact (congrArg SucCard (ih l J hj ht)).trans he.symm
  exact main n F h m G k e

#classicism_check seqEmpty_exists seqCons_exists seqCons_head seqCons_tail seqCons_not_empty
  seqCons_coext finiteSeq_nil finiteSeq_cons finiteSeq_induction finiteSeq_length_nat
  finiteSeq_members finiteSeq_cases finiteSeq_zero_iff finiteSeq_functional seqCons_injective
  finiteSeq_coext finiteSeq_length_unique
#classicism_types seqEmpty_exists seqCons_exists seqCons_head seqCons_tail seqCons_not_empty
  seqCons_coext finiteSeq_nil finiteSeq_cons finiteSeq_induction finiteSeq_length_nat
  finiteSeq_members finiteSeq_cases finiteSeq_zero_iff finiteSeq_functional seqCons_injective
  finiteSeq_coext finiteSeq_length_unique
end Classicism.MathematicalContingency
