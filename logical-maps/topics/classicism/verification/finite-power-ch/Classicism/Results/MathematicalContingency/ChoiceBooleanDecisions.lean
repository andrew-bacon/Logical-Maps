import Classicism.Results.MathematicalContingency.CountableChoiceFusion
import Classicism.Results.MathematicalContingency.BooleanDecisions

/-! Binary decisions using current relational choice rather than a well-order
of the forcing carrier. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]

/-- The new fusion step is certified separately from the historical CBA fact
that a single decision can always be made densely. -/
theorem binaryDecisions_of_dense_steps (hp : LowerPeano σ)
    (Q : τ → Prop) (E : τ → τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o i : β) (C : τ → β → Prop)
    (choice : P.RelationalChoice (((σ → Prop) → Prop) → τ → Prop) τ)
    (closed : @CountablyClosed σ τ _ _ Q E) (order : PartialOrderOn B R)
    (cones : DenseCones Q E B R o C)
    (steps : ∀ q x, Q q → B x → ∃ r, Q r ∧ E r q ∧
      ∀ c, C r c → DecidesAt B R o i c x) :
    @BinaryDecisionProperty σ β _ _ B R o i := by
  intro S hs b hb hbn
  obtain ⟨z,zc,hz,hzc,hzb⟩ := cones.2.2.2.1 b hb hbn
  let D := fun n q => ∀ x c, S n x → C q c → DecidesAt B R o i c x
  have dense : ∀ n q, LowerNat n → Q q → ∃ r, Q r ∧ E r q ∧ D n r := by
    intro n q hn hq
    obtain ⟨x,hx,hS⟩ := hs.2.1 n hn
    obtain ⟨r,hr,hrq,hd⟩ := steps q x hq hx
    exact ⟨r,hr,hrq,fun y c hy hc => (hs.2.2 n x y hS hy) ▸ hd c hc⟩
  have down : ∀ n q r, LowerNat n → Q q → Q r → E r q → D n q → D n r := by
    intro n q r _ hq _ hrq hd x c hS hC
    obtain ⟨d,_,hqd⟩ := cones.1.2.1 q hq
    have hcd := cones.2.2.1 q r d c hqd hC hrq
    obtain h | ⟨v,hv,hdv⟩ := hd x d hS hqd
    · exact Or.inl (order.2.2.2 c d x hcd h)
    · exact Or.inr ⟨v,hv,order.2.2.2 c d v hcd hdv⟩
  obtain ⟨q,hq,hqz,hd⟩ := countablyClosed_dense_family_of_relationalChoice hp Q E D
    choice closed dense down z hz
  obtain ⟨c,hc,hC⟩ := cones.1.2.1 q hq
  exact ⟨c,hc,cones.2.1 q c hC,
    order.2.2.2 c zc b (cones.2.2.1 z q zc c hzc hC hqz) hzb,
    fun n x hn hS => hd n hn x c hS hC⟩

theorem closure_binary_decisions_of_relationalChoice (hp : LowerPeano σ)
    (Q : τ → Prop) (E : τ → τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (o i : β) (C : τ → β → Prop)
    (choice : P.RelationalChoice (((σ → Prop) → Prop) → τ → Prop) τ)
    (closed : @CountablyClosed σ τ _ _ Q E)
    (cba : CBA B R) (endpoints : Endpoints B R o i)
    (comps : ∀ b, B b → ∃ d, ComplementAt B R o i b d)
    (cones : DenseCones Q E B R o C) : @BinaryDecisionProperty σ β _ _ B R o i := by
  apply binaryDecisions_of_dense_steps hp Q E B R o i C choice closed cba.1 cones
  intro q x hq hx
  obtain ⟨c,hc,hC⟩ := cones.1.2.1 q hq
  obtain ⟨v,hv,hnv,hvc,hdec⟩ := cba_nonzero_decision B R cba o i c x endpoints comps hc
    (cones.2.1 q c hC) hx
  obtain ⟨r,d,hr,hrq,hrd,hdv⟩ := cones.2.2.2.2 q c v hC hv hnv hvc
  exact ⟨r,hr,hrq,fun e he => (cones.1.2.2 r d e hrd he) ▸
    decidesAt_down B R cba.1 o i v d x hdv hdec⟩

theorem closure_binary_decisions_cba_of_relationalChoice (hp : LowerPeano σ)
    (Q : τ → Prop) (E : τ → τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (C : τ → β → Prop)
    (choice : P.RelationalChoice (((σ → Prop) → Prop) → τ → Prop) τ)
    (closed : @CountablyClosed σ τ _ _ Q E) (cba : CBA B R)
    (cones : ∀ o i, Endpoints B R o i → DenseCones Q E B R o C) :
    ∃ o i, Endpoints B R o i ∧ @BinaryDecisionProperty σ β _ _ B R o i := by
  obtain ⟨o,i,he,hcomp⟩ := cba.2.2.2.2
  exact ⟨o,i,he,closure_binary_decisions_of_relationalChoice hp Q E B R o i C
    choice closed cba he hcomp (cones o i he)⟩

#classicism_check binaryDecisions_of_dense_steps closure_binary_decisions_of_relationalChoice
  closure_binary_decisions_cba_of_relationalChoice
#classicism_types binaryDecisions_of_dense_steps closure_binary_decisions_of_relationalChoice
  closure_binary_decisions_cba_of_relationalChoice
end Classicism.MathematicalContingency.FinitePower
