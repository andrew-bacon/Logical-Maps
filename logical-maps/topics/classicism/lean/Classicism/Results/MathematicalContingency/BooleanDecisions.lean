import Classicism.Results.MathematicalContingency.CountableClosure

/-! Binary decisions from countable closure and the explicit basic-cone interface.
Regular-open completion itself is not constructed here. -/
namespace Classicism.MathematicalContingency
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]

def ComplementAt (B : β → Prop) (R : β → β → Prop) (o i x y : β) : Prop :=
  B y ∧ Meets B R x y o ∧ Joins B R x y i

def DecidesAt (B : β → Prop) (R : β → β → Prop) (o i c b : β) : Prop :=
  R c b ∨ ∃ d, ComplementAt B R o i b d ∧ R c d

def BinaryDecisionProperty (B : β → Prop) (R : β → β → Prop) (o i : β) : Prop :=
  ∀ S : ((σ → Prop) → Prop) → β → Prop, Maps S LowerNat B →
    ∀ b, B b → b ≠ o → ∃ c, B c ∧ c ≠ o ∧ R c b ∧
      ∀ n x, LowerNat n → S n x → DecidesAt B R o i c x

/-- The deferred completion must supply nonzero cones, monotonicity, density,
and refinement below a given condition. No order reflection is assumed. -/
def DenseCones (Q : τ → Prop) (E : τ → τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : τ → β → Prop) : Prop :=
  Maps C Q B ∧ (∀ q b, C q b → b ≠ o) ∧
  (∀ q r b c, C q b → C r c → E r q → R c b) ∧
  (∀ b, B b → b ≠ o → ∃ q c, Q q ∧ C q c ∧ R c b) ∧
  (∀ q b v, C q b → B v → v ≠ o → R v b →
    ∃ r c, Q r ∧ E r q ∧ C r c ∧ R c v)

theorem cba_meet_exists (B : β → Prop) (R : β → β → Prop) (h : CBA B R)
    (x y : β) (hx : B x) (hy : B y) : ∃ z, Meets B R x y z :=
  h.2.2.1 (fun u => u = x ∨ u = y)
    (fun u hu => hu.elim (fun e => e.symm ▸ hx) (fun e => e.symm ▸ hy))

theorem meet_top_self (B : β → Prop) (R : β → β → Prop)
    (hp : PartialOrderOn B R) (o i x : β) (he : Endpoints B R o i) (hx : B x) :
    Meets B R x i x := by
  refine ⟨hx,?_,?_⟩
  · intro u hu
    exact hu.elim (fun e => e.symm ▸ hp.2.1 x hx) (fun e => e.symm ▸ (he.2.2 x hx).2)
  · intro y _ hy
    exact hy x (Or.inl rfl)

/-- If x meets b only in zero, distributivity puts x below a complement of b. -/
theorem cba_disjoint_complement (B : β → Prop) (R : β → β → Prop)
    (h : CBA B R) (o i x b d : β) (he : Endpoints B R o i)
    (hx : B x) (hb : B b) (hd : ComplementAt B R o i b d)
    (hm : Meets B R x b o) : R x d := by
  obtain ⟨s,hs⟩ := cba_meet_exists B R h x d hx hd.1
  have hj := h.2.2.2.1 x b d i x o s hx hb hd.1 hd.2.2
    (meet_top_self B R h.1 o i x he hx) hm hs
  exact hj.2.2 d hd.1 (fun u hu =>
    hu.elim (fun e => e.symm ▸ (he.2.2 d hd.1).1)
      (fun e => e.symm ▸ hs.2.1 d (Or.inr rfl)))

theorem cba_nonzero_decision (B : β → Prop) (R : β → β → Prop)
    (h : CBA B R) (o i x b : β) (he : Endpoints B R o i)
    (comps : ∀ b, B b → ∃ d, ComplementAt B R o i b d)
    (hx : B x) (hn : x ≠ o) (hb : B b) :
    ∃ v, B v ∧ v ≠ o ∧ R v x ∧ DecidesAt B R o i v b := by
  obtain ⟨v,hv⟩ := cba_meet_exists B R h x b hx hb
  obtain hz | hnz := em (v = o)
  · obtain ⟨d,hd⟩ := comps b hb
    exact ⟨x,hx,hn,h.1.2.1 x hx,Or.inr ⟨d,hd,
      cba_disjoint_complement B R h o i x b d he hx hb hd (hz ▸ hv)⟩⟩
  · exact ⟨v,hv.1,hnz,hv.2.1 x (Or.inl rfl),Or.inl (hv.2.1 b (Or.inr rfl))⟩

theorem decidesAt_down (B : β → Prop) (R : β → β → Prop)
    (hp : PartialOrderOn B R) (o i c d b : β) (hcd : R d c)
    (h : DecidesAt B R o i c b) : DecidesAt B R o i d b := by
  obtain h | ⟨e,he,hce⟩ := h
  · exact Or.inl (hp.2.2.2 d c b hcd h)
  · exact Or.inr ⟨e,he,hp.2.2.2 d c e hcd hce⟩

/-- The closure lemma, with the deferred regular-open facts exposed as DenseCones. -/
theorem closure_binary_decisions (hp : LowerPeano σ)
    (Q : τ → Prop) (E L : τ → τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o i : β) (C : τ → β → Prop)
    (hw : WellOrderOn Q L) (hc : @CountablyClosed σ τ _ _ Q E)
    (hb : CBA B R) (he : Endpoints B R o i)
    (comps : ∀ b, B b → ∃ d, ComplementAt B R o i b d)
    (cones : DenseCones Q E B R o C) : @BinaryDecisionProperty σ β _ _ B R o i := by
  intro S hs b hbB hbn
  obtain ⟨z,zc,hzB,hzC,hzb⟩ := cones.2.2.2.1 b hbB hbn
  let D := fun n q => ∀ x c, S n x → C q c → DecidesAt B R o i c x
  have dense : ∀ n q, LowerNat n → Q q → ∃ r, Q r ∧ E r q ∧ D n r := by
    intro n q hn hq
    obtain ⟨x,hx,hS⟩ := hs.2.1 n hn
    obtain ⟨c,hcB,hC⟩ := cones.1.2.1 q hq
    obtain ⟨v,hv,hnv,hvc,hdec⟩ := cba_nonzero_decision B R hb o i c x he comps hcB
      (cones.2.1 q c hC) hx
    obtain ⟨r,d,hr,hrq,hrd,hdv⟩ := cones.2.2.2.2 q c v hC hv hnv hvc
    refine ⟨r,hr,hrq,?_⟩
    intro y e hy heC
    have ey := hs.2.2 n x y hS hy
    have ee := cones.1.2.2 r d e hrd heC
    subst y
    subst e
    exact decidesAt_down B R hb.1 o i v d x hdv hdec
  have down : ∀ n q r, LowerNat n → Q q → Q r → E r q → D n q → D n r := by
    intro n q r _ hq _ hrq hd x c hS hC
    obtain ⟨d,_,hqd⟩ := cones.1.2.1 q hq
    exact decidesAt_down B R hb.1 o i d c x (cones.2.2.1 q r d c hqd hC hrq)
      (hd x d hS hqd)
  obtain ⟨q,hq,hqz,hd⟩ := countablyClosed_dense_family hp Q E L D hw hc dense down z hzB
  obtain ⟨c,hcB,hC⟩ := cones.1.2.1 q hq
  exact ⟨c,hcB,cones.2.1 q c hC,
    hb.1.2.2.2 c _ b (cones.2.2.1 z q _ c hzC hC hqz) hzb,
    fun n x hn hS => hd n hn x c hS hC⟩

/-- CBA already supplies the endpoints and complements used above. -/
theorem closure_binary_decisions_cba (hp : LowerPeano σ)
    (Q : τ → Prop) (E L : τ → τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (C : τ → β → Prop)
    (hw : WellOrderOn Q L) (hc : @CountablyClosed σ τ _ _ Q E)
    (hb : CBA B R)
    (cones : ∀ o i, Endpoints B R o i → DenseCones Q E B R o C) :
    ∃ o i, Endpoints B R o i ∧ @BinaryDecisionProperty σ β _ _ B R o i := by
  obtain ⟨o,i,he,hcomp⟩ := hb.2.2.2.2
  exact ⟨o,i,he,closure_binary_decisions hp Q E L B R o i C hw hc hb he hcomp (cones o i he)⟩

#classicism_check cba_meet_exists meet_top_self cba_disjoint_complement cba_nonzero_decision decidesAt_down closure_binary_decisions closure_binary_decisions_cba
#classicism_types cba_meet_exists meet_top_self cba_disjoint_complement cba_nonzero_decision decidesAt_down closure_binary_decisions closure_binary_decisions_cba
end Classicism.MathematicalContingency
