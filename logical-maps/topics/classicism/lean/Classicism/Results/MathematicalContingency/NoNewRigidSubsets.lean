import Classicism.Results.MathematicalContingency.DecisionRepresentation
import Classicism.Results.MathematicalContingency.StableTransport
import Classicism.Results.MathematicalContingency.NaturalModal

/-! Forcing-relative preservation of rigid subsets. All additional principles are premises.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β σ : Type} [Ty α] [Ty β] [Ty σ]

def OutsideRigidPower (A : α → Prop) (R₀ : (α → Prop) → Prop) (X : α → Prop) : Prop :=
  ∃ U, RigidPower A U ∧ (U ≡ X) ∧ ¬ R₀ U

theorem rigidPower_member_persistent (A S : α → Prop) (ha : Rigid A)
    (hs : RigidPower A S) : □ (RigidPower A S) :=
  (box_and_eq _ _).mpr ⟨(box_and_eq _ _).mpr ⟨modal_four _ hs.1.1,modal_four _ hs.1.2⟩,
    restricted_barcan_unary S A hs.1 (fun x hx => box_elim ha.1 x (hs.2 x hx))⟩

theorem rigidPower_old_members (A : α → Prop) (R₀ : (α → Prop) → Prop)
    (ha : Rigid A) (hr : Rigid R₀) (co : ∀ U, RigidPower A U ↔ R₀ U) :
    □ (∀ U, R₀ U → RigidPower A U) :=
  restricted_barcan_unary R₀ (RigidPower A) hr
    (fun U hU => rigidPower_member_persistent A U ha ((co U).mpr hU))

/-- Decisions reconstruct a rigid representative on a rigid, internally ND carrier. -/
theorem decisions_reconstruct (A X : α → Prop) (q : Prop)
    (ha : Rigid A) (nd : DomainND A) (rc : Classicism.P.RigidComprehension (α → Prop))
    (dec : ∀ a, A a → EntailmentOrder q (X a) ∨ EntailmentOrder q (¬ X a)) :
    ∃ S, RigidPower A S ∧ EntailmentOrder q (∀ a, A a → (X a ↔ S a)) := by
  obtain ⟨S,hs,hco⟩ := rc (fun a => A a ∧ EntailmentOrder q (X a))
  have sub : ∀ a, S a → A a := fun a h => ((hco a).mpr h).1
  have point : ∀ a, A a → □ (q → (X a ↔ S a)) := by
    intro a haA
    obtain hp | hn := dec a haA
    · have hS : S a := (hco a).mp ⟨haA,hp⟩
      exact modal_K _ _ (modal_K _ _
        (nec% (fun (h : q → X a) (s : S a) (hq : q) => (show X a ↔ S a from ⟨fun _ => s,fun _ => h hq⟩)))
        hp) (box_elim hs.1 a hS)
    · obtain hS | hnS := em (S a)
      · have hp := ((hco a).mpr hS).2
        exact modal_K _ _ (modal_K _ _
          (nec% (fun (h : q → X a) (k : q → ¬ X a) (hq : q) => (show X a ↔ S a from (k hq (h hq)).elim))) hp) hn
      · exact modal_K _ _ (modal_K _ _
          (nec% (fun (h : q → ¬ X a) (k : ¬ S a) (hq : q) =>
            (show X a ↔ S a from ⟨fun hx => (h hq hx).elim,fun hs => (k hs).elim⟩))) hn)
          (rigid_subset_negative A S nd hs sub a haA hnS)
  exact ⟨S,⟨hs,sub⟩,modal_K _ _
    (nec% (fun (h : ∀ a, A a → q → (X a ↔ S a)) (hq : q) a ha => h a ha hq))
    (restricted_barcan_unary A (fun a => q → (X a ↔ S a)) ha point)⟩

theorem outsideRigidPower_coext (A : α → Prop) (R₀ : (α → Prop) → Prop)
    (X Y : α → Prop) (h : X ≡ Y) : OutsideRigidPower A R₀ X ↔ OutsideRigidPower A R₀ Y := by
  constructor
  · intro hh
    obtain ⟨U,hU,hUX,hn⟩ := hh
    exact ⟨U,hU,fun a => (hUX a).trans (h a),hn⟩
  · intro hh
    obtain ⟨U,hU,hUY,hn⟩ := hh
    exact ⟨U,hU,fun a => (hUY a).trans (h a).symm,hn⟩

theorem outsideRigidPower_of_failure (A : α → Prop) (R₀ : (α → Prop) → Prop)
    (h : ¬ ∀ U, RigidPower A U → R₀ U) : ∃ X, OutsideRigidPower A R₀ X := by
  obtain ⟨U,hU⟩ := (not_forall_eq (fun U => RigidPower A U → R₀ U)).mp h
  have hp : RigidPower A U := (em (RigidPower A U)).elim id
    (fun hn => (hU (fun hu => (hn hu).elim)).elim)
  exact ⟨U,U,hp,fun _ => Iff.rfl,fun hr => hU (fun _ => hr)⟩

/-- Current logical contradiction, later lifted under a deciding proposition. -/
theorem outsideRigidPower_contradiction (A S X : α → Prop) (R₀ : (α → Prop) → Prop)
    (hs : RigidPower A S) (hr : R₀ S) (hx : OutsideRigidPower A R₀ X)
    (he : ∀ a, A a → (X a ↔ S a)) : False := by
  obtain ⟨U,hU,hUX,hn⟩ := hx
  have e : U = S := rigid_eq_of_coext U S hU.1 hs.1 (by
    intro a
    constructor
    · intro hu
      exact (he a (hU.2 a hu)).mp ((hUX a).mp hu)
    · intro hS
      exact (hUX a).mpr ((he a (hs.2 a hS)).mpr hS))
  exact hn (e.symm ▸ hr)

/-- No new members under P; this is not an unrestricted Rigid Power theorem. -/
theorem localDecisions_no_new (A : α → Prop) (R₀ : (α → Prop) → Prop) (P : Prop)
    (ha : Rigid A) (nd : DomainND A) (hr : Rigid R₀)
    (co : ∀ U, RigidPower A U ↔ R₀ U)
    (rc : Classicism.P.RigidComprehension (α → Prop)) (ic : Classicism.P.IntensionalChoice (α → Prop))
    (dec : LocalDecisions A P) : EntailmentOrder P (∀ U, RigidPower A U → R₀ U) := by
  apply (entailment_counterexample_false P (∀ U, RigidPower A U → R₀ U)).mpr
  let Q := P ∧ ¬ ∀ U, RigidPower A U → R₀ U
  obtain hzero | hn := em (Q = False)
  · exact hzero
  · have hex : □ (Q → ∃ X, OutsideRigidPower A R₀ X) :=
      nec% (fun h : Q => outsideRigidPower_of_failure A R₀ h.2)
    obtain ⟨X,hX⟩ := local_selection ic Q (OutsideRigidPower A R₀)
      (nec% (outsideRigidPower_coext A R₀)) hex
    obtain ⟨q,hnq,hqQ,hdec⟩ := dec X Q hn (nec% (fun h : Q => h.1))
    obtain ⟨S,hS,he⟩ := decisions_reconstruct A X q ha nd rc hdec
    have hqX := entailment_trans q Q (OutsideRigidPower A R₀ X) hqQ hX
    have hfalse : □ (¬ q) := modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (hs : RigidPower A S) (hr : R₀ S)
        (hx : q → OutsideRigidPower A R₀ X) (he : q → ∀ a, A a → (X a ↔ S a)) (hq : q) =>
          outsideRigidPower_contradiction A S X R₀ hs hr (hx hq) (he hq)))
      (rigidPower_member_persistent A S ha hS)) (box_elim hr.1 S ((co S).mp hS))) hqX) he
    exact (hnq ((box_not_eq q).mp hfalse)).elim

theorem localDecisions_preserves_power (A : α → Prop) (R₀ : (α → Prop) → Prop) (P : Prop)
    (ha : Rigid A) (nd : DomainND A) (hr : Rigid R₀)
    (co : ∀ U, RigidPower A U ↔ R₀ U)
    (rc : Classicism.P.RigidComprehension (α → Prop)) (ic : Classicism.P.IntensionalChoice (α → Prop))
    (dec : LocalDecisions A P) : EntailmentOrder P (∀ U, RigidPower A U ↔ R₀ U) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (h : P → ∀ U, RigidPower A U → R₀ U) (k : ∀ U, R₀ U → RigidPower A U)
      (hp : P) U => (show RigidPower A U ↔ R₀ U from ⟨h hp U,k U⟩)))
    (localDecisions_no_new A R₀ P ha nd hr co rc ic dec)) (rigidPower_old_members A R₀ ha hr co)

theorem binaryDecisions_no_new_naturals
    (B : β → Prop) (R : β → β → Prop) (F : β → Prop → Prop) (P : Prop) (o i : β)
    (R₀ : (((σ → Prop) → Prop) → Prop) → Prop)
    (hi : DraftBoxInfinity σ) (rigidN : Rigid (@LowerNat σ _))
    (hr : Rigid R₀) (co : ∀ U, RigidPower LowerNat U ↔ R₀ U)
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (ic : Classicism.P.IntensionalChoice (((σ → Prop) → Prop) → Prop))
    (hf : OrderIso F B R (Below P) EntailmentOrder) (ho : F o False)
    (hd : @BinaryDecisionProperty σ β _ _ B R o i) :
    EntailmentOrder P (∀ U, RigidPower LowerNat U ↔ R₀ U) :=
  localDecisions_preserves_power LowerNat R₀ P rigidN (lowerNat_nd hi) hr co rc ic
    (binaryDecisions_local B R F P o i hf ho hd)

/-- Higher-type RC supplies the current rigidification; the theorem preserves it under P. -/
theorem binaryDecisions_preserves_rigidification
    (B : β → Prop) (R : β → β → Prop) (F : β → Prop → Prop) (P : Prop) (o i : β)
    (hi : DraftBoxInfinity σ) (rigidN : Rigid (@LowerNat σ _))
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (rc₀ : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (ic : Classicism.P.IntensionalChoice (((σ → Prop) → Prop) → Prop))
    (hf : OrderIso F B R (Below P) EntailmentOrder) (ho : F o False)
    (hd : @BinaryDecisionProperty σ β _ _ B R o i) :
    ∃ R₀ : (((σ → Prop) → Prop) → Prop) → Prop, Rigid R₀ ∧ (∀ U, RigidPower LowerNat U ↔ R₀ U) ∧
      EntailmentOrder P (∀ U, RigidPower LowerNat U ↔ R₀ U) := by
  obtain ⟨R₀,hr,co⟩ := rc₀ (RigidPower (@LowerNat σ _))
  exact ⟨R₀,hr,co,binaryDecisions_no_new_naturals B R F P o i R₀ hi rigidN hr co rc ic hf ho hd⟩

#classicism_check rigidPower_member_persistent rigidPower_old_members decisions_reconstruct outsideRigidPower_coext outsideRigidPower_of_failure outsideRigidPower_contradiction localDecisions_no_new localDecisions_preserves_power binaryDecisions_no_new_naturals binaryDecisions_preserves_rigidification
#classicism_types rigidPower_member_persistent rigidPower_old_members decisions_reconstruct outsideRigidPower_coext outsideRigidPower_of_failure outsideRigidPower_contradiction localDecisions_no_new localDecisions_preserves_power binaryDecisions_no_new_naturals binaryDecisions_preserves_rigidification
end Classicism.MathematicalContingency
