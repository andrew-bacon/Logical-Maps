import Classicism.MathematicalContingency.FiniteSequences

/-! Generic relational coding of finite sequences.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
Coding hypotheses are explicit. Equality of codes recovers coextension of graphs;
identity of graph objects is used only when both are rigid. -/
namespace Classicism.MathematicalContingency
variable {σ τ κ : Type} [Ty σ] [Ty τ] [Ty κ]

def SequenceCode (A : τ → Prop) (B : κ → Prop) (z : κ) (C : τ → κ → κ → Prop)
    (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) (c : κ) : Prop :=
  ∀ P : ((σ → Prop) → Prop) → (((σ → Prop) → Prop) → τ → Prop) → κ → Prop,
    (∀ F, B z → SeqEmpty F → P (AtLeastZero σ) F z) →
    (∀ n F x G c d, LowerNat n → A x → B c → B d → SeqCons x F G → C x c d →
      P n F c → P (SucCard n) G d) → P n F c

variable (A : τ → Prop) (B : κ → Prop) (z : κ) (C : τ → κ → κ → Prop)

theorem sequenceCode_nil (F : ((σ → Prop) → Prop) → τ → Prop) (hz : B z) (he : SeqEmpty F) :
    SequenceCode A B z C (AtLeastZero σ) F z := fun _ h0 _ => h0 F hz he

theorem sequenceCode_cons (n : (σ → Prop) → Prop)
    (F G : ((σ → Prop) → Prop) → τ → Prop) (x : τ) (c d : κ)
    (hn : LowerNat n) (hx : A x) (hc : B c) (hd : B d)
    (hcons : SeqCons x F G) (hC : C x c d) (h : SequenceCode A B z C n F c) :
    SequenceCode A B z C (SucCard n) G d :=
  fun P h0 hs => hs n F x G c d hn hx hc hd hcons hC (h P h0 hs)

theorem sequenceCode_induction
    (P : ((σ → Prop) → Prop) → (((σ → Prop) → Prop) → τ → Prop) → κ → Prop)
    (h0 : ∀ F, B z → SeqEmpty F → P (AtLeastZero σ) F z)
    (step : ∀ n F x G c d, LowerNat n → A x → B c → B d → SeqCons x F G → C x c d →
      SequenceCode A B z C n F c → P n F c → P (SucCard n) G d)
    (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) (c : κ)
    (h : SequenceCode A B z C n F c) : P n F c :=
  (h (fun n F c => SequenceCode A B z C n F c ∧ P n F c)
    (fun F hz he => ⟨sequenceCode_nil A B z C F hz he,h0 F hz he⟩)
    (fun n F x G c d hn hx hc hd hcons hC ih =>
      ⟨sequenceCode_cons A B z C n F G x c d hn hx hc hd hcons hC ih.1,
       step n F x G c d hn hx hc hd hcons hC ih.1 ih.2⟩)).2

theorem sequenceCode_data (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) (c : κ) (h : SequenceCode A B z C n F c) :
    FiniteSeq A n F ∧ B c :=
  h (fun n F c => FiniteSeq A n F ∧ B c)
    (fun F hz he => ⟨finiteSeq_nil A F he,hz⟩)
    (fun n F x G c d hn hx hc hd hcons _ ih => ⟨finiteSeq_cons A n F G x hn hx hcons ih.1,hd⟩)

theorem sequenceCode_cases (n : (σ → Prop) → Prop)
    (F : ((σ → Prop) → Prop) → τ → Prop) (c : κ) (h : SequenceCode A B z C n F c) :
    (n = AtLeastZero σ ∧ SeqEmpty F ∧ c = z ∧ B z) ∨
    ∃ m H x b, LowerNat m ∧ A x ∧ B b ∧ B c ∧ SeqCons x H F ∧ C x b c ∧
      SequenceCode A B z C m H b ∧ n = SucCard m :=
  sequenceCode_induction A B z C
    (fun n F c => (n = AtLeastZero σ ∧ SeqEmpty F ∧ c = z ∧ B z) ∨
      ∃ m H x b, LowerNat m ∧ A x ∧ B b ∧ B c ∧ SeqCons x H F ∧ C x b c ∧
        SequenceCode A B z C m H b ∧ n = SucCard m)
    (fun F hz he => Or.inl ⟨rfl,he,rfl,hz⟩)
    (fun m H x G b c hm hx hb hc hcons hC hs _ => Or.inr ⟨m,H,x,b,hm,hx,hb,hc,hcons,hC,hs,rfl⟩)
    n F c h

theorem sequenceCode_total (hz : B z)
    (total : ∀ x, A x → ∀ c, B c → ∃ d, B d ∧ C x c d)
    (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) (h : FiniteSeq A n F) :
    ∃ c, B c ∧ SequenceCode A B z C n F c := by
  apply finiteSeq_induction A (fun n F => ∃ c, B c ∧ SequenceCode A B z C n F c) ?_ ?_ n F h
  · intro F he
    exact ⟨z,hz,sequenceCode_nil A B z C F hz he⟩
  · intro n F x G hn hx hcons _ ih
    obtain ⟨c,hc,hcode⟩ := ih
    obtain ⟨d,hd,hC⟩ := total x hx c hc
    exact ⟨d,hd,sequenceCode_cons A B z C n F G x c d hn hx hc hd hcons hC hcode⟩

theorem sequenceCode_coext (n : (σ → Prop) → Prop)
    (F G : ((σ → Prop) → Prop) → τ → Prop) (c : κ) (h : SequenceCode A B z C n F c)
    (e : ∀ i x, F i x ↔ G i x) : SequenceCode A B z C n G c := by
  obtain ⟨hn,he,hc,hz⟩ | ⟨m,H,x,b,hm,hx,hb,hc,hcons,hC,hs,hn⟩ := sequenceCode_cases A B z C n F c h
  · subst n; subst c
    exact sequenceCode_nil A B z C G hz (fun i x hg => he i x ((e i x).mpr hg))
  · subst n
    exact sequenceCode_cons A B z C m H G x b c hm hx hb hc
      (fun i y => (e i y).symm.trans (hcons i y)) hC hs

theorem sequenceCode_functional (hp : LowerPeano σ)
    (functional : ∀ x c d e, C x c d → C x c e → d = e)
    (n m : (σ → Prop) → Prop) (F G : ((σ → Prop) → Prop) → τ → Prop) (c d : κ)
    (h : SequenceCode A B z C n F c) (k : SequenceCode A B z C m G d)
    (e : ∀ i x, F i x ↔ G i x) : c = d := by
  have main : ∀ (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) (c : κ),
      SequenceCode A B z C n F c → ∀ m G d, SequenceCode A B z C m G d →
      (∀ i x, F i x ↔ G i x) → c = d := by
    intro n F c h
    apply sequenceCode_induction A B z C (fun _ F c => ∀ m G d, SequenceCode A B z C m G d →
      (∀ i x, F i x ↔ G i x) → c = d) ?_ ?_ n F c h
    · intro F hz he m G d hg e
      obtain ⟨_,_,hd,_⟩ | ⟨l,H,x,b,hl,hx,hb,hd,hcons,hC,hs,hm⟩ := sequenceCode_cases A B z C m G d hg
      · exact hd.symm
      · exact (he _ x ((e _ x).mpr ((hcons _ x).mpr (Or.inl ⟨rfl,rfl⟩)))).elim
    · intro n F x G c d hn hx hc hd hcons hC hs ih m H v hh e
      obtain ⟨_,hempty,_,_⟩ | ⟨l,J,y,b,hl,hy,hb,hv,hcons',hC',hs',hm⟩ := sequenceCode_cases A B z C m H v hh
      · exact (hempty _ x ((e _ x).mp ((hcons _ x).mpr (Or.inl ⟨rfl,rfl⟩)))).elim
      · have hf := (sequenceCode_data A B z C n F c hs).1
        have hj := (sequenceCode_data A B z C l J b hs').1
        obtain ⟨ex,et⟩ := seqCons_injective hp x y F J G H
          (fun i a hF => (finiteSeq_members A n F hf i a hF).1)
          (fun i a hJ => (finiteSeq_members A l J hj i a hJ).1) hcons hcons' e
        have ec := ih l J b hs' et
        subst y; subst b
        exact functional x c d v hC hC'
  exact main n F c h m G d k e

theorem sequenceCode_injective
    (disjoint : ∀ x c, ¬ C x c z)
    (injective : ∀ x y c d v, C x c v → C y d v → x = y ∧ c = d)
    (n m : (σ → Prop) → Prop) (F G : ((σ → Prop) → Prop) → τ → Prop) (c : κ)
    (h : SequenceCode A B z C n F c) (k : SequenceCode A B z C m G c) :
    n = m ∧ ∀ i x, F i x ↔ G i x := by
  have main : ∀ (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) (c : κ),
      SequenceCode A B z C n F c → ∀ m G, SequenceCode A B z C m G c →
      n = m ∧ ∀ i x, F i x ↔ G i x := by
    intro n F c h
    apply sequenceCode_induction A B z C (fun n F c => ∀ m G, SequenceCode A B z C m G c →
      n = m ∧ ∀ i x, F i x ↔ G i x) ?_ ?_ n F c h
    · intro F hz he m G hg
      obtain ⟨hm,hG,_,_⟩ | ⟨l,H,x,b,hl,hx,hb,hd,hcons,hC,hs,hm⟩ := sequenceCode_cases A B z C m G z hg
      · exact ⟨hm.symm,fun i x => ⟨fun hf => (he i x hf).elim,fun hg => (hG i x hg).elim⟩⟩
      · exact (disjoint x b hC).elim
    · intro n F x G c d hn hx hc hd hcons hC hs ih m H hh
      obtain ⟨_,_,ed,_⟩ | ⟨l,J,y,b,hl,hy,hb,hd',hcons',hC',hs',hm⟩ := sequenceCode_cases A B z C m H d hh
      · exact (disjoint x c (ed ▸ hC)).elim
      · obtain ⟨ex,ec⟩ := injective x y c b d hC hC'
        subst y; subst b
        obtain ⟨en,et⟩ := ih l J hs'
        exact ⟨(congrArg SucCard en).trans hm.symm,seqCons_coext x F J G H hcons hcons' et⟩
  exact main n F c h m G k

def RigidFiniteSeq (A : τ → Prop) (F : ((σ → Prop) → Prop) → τ → Prop) : Prop :=
  Rigid F ∧ ∃ n, FiniteSeq A n F

theorem finiteSeq_rigid_representative (rc : P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop))
    (A : τ → Prop) (n : (σ → Prop) → Prop) (F : ((σ → Prop) → Prop) → τ → Prop)
    (h : FiniteSeq A n F) : ∃ G, Rigid G ∧ FiniteSeq A n G ∧ ∀ i x, F i x ↔ G i x := by
  obtain ⟨G,hG,e⟩ := rc F
  exact ⟨G,hG,finiteSeq_coext A n F G h e,e⟩

theorem sequenceCode_embedding (hp : LowerPeano σ) (hz : B z)
    (total : ∀ x, A x → ∀ c, B c → ∃ d, B d ∧ C x c d)
    (functional : ∀ x c d e, C x c d → C x c e → d = e)
    (disjoint : ∀ x c, ¬ C x c z)
    (injective : ∀ x y c d v, C x c v → C y d v → x = y ∧ c = d) :
    Embeds (@RigidFiniteSeq σ τ _ _ A) B := by
  refine ⟨fun F c => RigidFiniteSeq A F ∧ ∃ n, SequenceCode A B z C n F c,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro F c h
    obtain ⟨n,hn⟩ := h.2
    exact ⟨h.1,(sequenceCode_data A B z C n F c hn).2⟩
  · intro F hF
    obtain ⟨n,hn⟩ := hF.2
    obtain ⟨c,hc,hcode⟩ := sequenceCode_total A B z C hz total n F hn
    exact ⟨c,hc,hF,n,hcode⟩
  · intro F c d hc hd
    obtain ⟨n,hn⟩ := hc.2
    obtain ⟨m,hm⟩ := hd.2
    exact sequenceCode_functional A B z C hp functional n m F F c d hn hm (fun _ _ => Iff.rfl)
  · intro F G c hf hg
    obtain ⟨n,hn⟩ := hf.2
    obtain ⟨m,hm⟩ := hg.2
    have e := (sequenceCode_injective A B z C disjoint injective n m F G c hn hm).2
    exact rigid_eq_of_coext F G hf.1.1 hg.1.1 e

#classicism_check sequenceCode_nil sequenceCode_cons sequenceCode_induction sequenceCode_data
  sequenceCode_cases sequenceCode_total sequenceCode_coext sequenceCode_functional
  sequenceCode_injective finiteSeq_rigid_representative sequenceCode_embedding
#classicism_types sequenceCode_nil sequenceCode_cons sequenceCode_induction sequenceCode_data
  sequenceCode_cases sequenceCode_total sequenceCode_coext sequenceCode_functional
  sequenceCode_injective finiteSeq_rigid_representative sequenceCode_embedding
end Classicism.MathematicalContingency
