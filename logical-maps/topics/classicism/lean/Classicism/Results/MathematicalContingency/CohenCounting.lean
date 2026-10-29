import Classicism.Results.MathematicalContingency.AntichainCounting
import Classicism.Results.MathematicalContingency.UniformCCC
namespace Classicism.MathematicalContingency
variable {σ τ α β γ : Type} [Ty σ] [Ty τ] [Ty α] [Ty β] [Ty γ]

/-- The uniform CCC counting bound for current serial proposition-valued relations. -/
theorem cohen_serial_embeds_product (hp : LowerPeano σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (A : α → Prop) (B : β → Prop) (L : β → β → Prop) (D : α → β → Prop)
    (below : ∀ x y, A x → B y → Below P (D x y))
    (disjoint : ∀ x z y, A x → A z → B y → x ≠ z → □ (¬ (D x y ∧ D z y)))
    (hw : WellOrderOn B L) (serial : ∀ x, A x → ∃ y, B y ∧ D x y ≠ False)
    (rc : Classicism.P.RigidComprehension (β → ((σ → Prop) → Prop) → Prop)) :
    Embeds A (RelProduct B (@LowerNat σ _)) :=
  antichain_serial_embeds_product A B LowerNat L D H R F P o hf ho below disjoint
    (uniformCCC hp I rcC LC H R o C hH hwC hc B) hw serial rc

/-- If the current cardinal bound forbids counting A into B times N, possible coverage is zero. -/
theorem cohen_cover_cardinality_obstruction (hp : LowerPeano σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (A : α → Prop) (B : β → Prop) (L : β → β → Prop) (D : α → β → Prop) (Q : Prop)
    (below : ∀ x y, A x → B y → Below P (D x y))
    (disjoint : ∀ x z y, A x → A z → B y → x ≠ z → □ (¬ (D x y ∧ D z y)))
    (hw : WellOrderOn B L) (hb : Rigid B)
    (cover : ∀ x, A x → EntailmentOrder Q (∃ y, B y ∧ D x y))
    (rc : Classicism.P.RigidComprehension (β → ((σ → Prop) → Prop) → Prop))
    (large : ¬ Embeds A (RelProduct B (@LowerNat σ _))) : Q = False := by
  apply (em (Q = False)).elim id
  intro hn
  exact (large (cohen_serial_embeds_product hp I rcC LC H R o C hH hwC hc F P hf ho
    A B L D below disjoint hw (rigid_nonzero_serial A B D Q hb hn cover) rc)).elim

#classicism_check cohen_serial_embeds_product cohen_cover_cardinality_obstruction
#classicism_types cohen_serial_embeds_product cohen_cover_cardinality_obstruction
end Classicism.MathematicalContingency
