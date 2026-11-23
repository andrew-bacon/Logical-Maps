import Classicism.Results.MathematicalContingency.HartogsDistinctness
import Classicism.Results.MathematicalContingency.HartogsTheorem
import Classicism.Results.MathematicalContingency.StableMaps

/-! The stable index uses the original inductive order types directly.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

/-- RC upgrades the weakly rigid segment by identifying its rigid representative. -/
theorem stable_segment_rigid (rc : P.RigidComprehension (σ → Prop))
    (A : σ → Prop) (R : σ → σ → Prop) (hs : StableOrder A R) (a : σ) (ha : A a) :
    Rigid (Segment A R a) := by
  have hw := stable_segment_weaklyRigid A R hs a ha
  obtain ⟨B,hB,e⟩ := rc (Segment A R a)
  have ab : □ (∀ x, Segment A R a x → B x) :=
    hw.2 B (fun x hx => box_elim hB.1 x ((e x).mp hx))
  have ba : □ (∀ x, B x → Segment A R a x) :=
    restricted_barcan_unary B (Segment A R a) hB (fun x hx => hw.1 x ((e x).mpr hx))
  have eq : Segment A R a = B := intensionality _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (ab : ∀ x, Segment A R a x → B x) (ba : ∀ x, B x → Segment A R a x)
      x => (show Segment A R a x ↔ B x from ⟨ab x,ba x⟩))) ab) ba)
  exact eq.symm ▸ hB

/-- A rigid presentation of a current order, with necessary bounds on its segments. -/
def StableIndexPresentation {τ : Type} [Ty τ] (D : τ → Prop)
    (H A : σ → Prop) (R L : σ → σ → Prop) : Prop :=
  Rigid A ∧ Rigid L ∧ (∀ x, A x ↔ H x) ∧ (∀ x y, L x y ↔ R x y) ∧
  DomainND A ∧ □ (WellOrderOn A L) ∧ ¬ Embeds A D ∧
  □ (∀ x, A x → Embeds (Segment A L x) D)

/-- Transport is proved at arbitrary carrier types before the Hartogs specialization. -/
theorem stable_index_presentation {τ : Type} [Ty τ]
    (D : τ → Prop) (H : σ → Prop) (R : σ → σ → Prop)
    (hd : Rigid D) (nd : DomainND D) (ndH : DomainND H)
    (hwH : WellOrderOn H R) (large : ¬ Embeds H D)
    (small : ∀ x, H x → Embeds (Segment H R x) D)
    (rcH : P.RigidComprehension (σ → Prop))
    (rcL : P.RigidComprehension (σ → σ → Prop))
    (rcMap : P.RigidComprehension (σ → τ → Prop)) :
    ∃ A L, StableIndexPresentation D H A R L := by
  obtain ⟨A,hA,eA⟩ := rcH H
  obtain ⟨L,hL,eL⟩ := rcL R
  have ndA : DomainND A := fun x y hx hy => ndH x y ((eA x).mpr hx) ((eA y).mpr hy)
  have hw := wellOrder_coext H A R L hwH eA eL
  have hs := rigid_wellOrder_stable A L hw hA hL ndA
  refine ⟨A,L,hA,hL,(fun x => (eA x).symm),(fun x y => (eL x y).symm),ndA,hs.1,?_,?_⟩
  · intro he
    exact large (embeds_trans H A D (embeds_of_subset H A (fun x hx => (eA x).mp hx)) he)
  · apply restricted_barcan_unary A (fun x => Embeds (Segment A L x) D) hA
    intro x hx
    have emb : Embeds (Segment A L x) D :=
      embeds_trans _ (Segment H R x) D
        (embeds_of_subset _ _ (fun y hy => ⟨(eA y).mpr hy.1,(eL y x).mpr hy.2⟩))
        (small x ((eA x).mpr hx))
    obtain ⟨F,_,hf⟩ := embedding_has_necessary_rigid_witness (Segment A L x) D
      (stable_segment_rigid rcH A L hs x hx) hd
      (fun y z hy hz => ndA y z hy.1 hz.1) nd rcMap emb
    exact modal_K _ _ (nec% (fun (hi : Injects F (Segment A L x) D) =>
      (show Embeds (Segment A L x) D from ⟨F,hi⟩))) hf

/-- Coextension is current; necessary uncountability and rigidity of H(D) are not asserted. -/
def StableHartogsPresentation (D : σ → Prop) (A : OrdinalCarrier σ → Prop)
    (L : OrdinalCarrier σ → OrdinalCarrier σ → Prop) : Prop :=
  StableIndexPresentation D (HartogsCarrier D) A (HartogsOrder D) L

theorem stable_hartogs_presentation
    (D : σ → Prop) (hd : Rigid D) (nd : DomainND D)
    (rcF : P.RigidComprehension (σ → Prop))
    (rcR : P.RigidComprehension (σ → σ → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (rcL : P.RigidComprehension (OrdinalCarrier σ → OrdinalCarrier σ → Prop))
    (rcMap : P.RigidComprehension (OrdinalCarrier σ → σ → Prop)) :
    ∃ A L, StableHartogsPresentation D A L :=
  stable_index_presentation D (HartogsCarrier D) (HartogsOrder D) hd nd
    (hartogsCarrier_nd rcF rcR D nd) (hartogs_wellOrder rcH D)
    (inductive_hartogs rcH D).2.1 (hartogs_segment_embeds D) rcH rcL rcMap

set_option synthInstance.maxSize 2000 in
/-- The stable countable-segment index, with rigidity of N explicitly deferred. -/
theorem natural_stable_hartogs_presentation (hi : DraftBoxInfinity σ)
    (rigidN : Rigid (@LowerNat σ _))
    (rcF : P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (rcR : P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rcL : P.RigidComprehension
      (OrdinalCarrier ((σ → Prop) → Prop) → OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rcMap : P.RigidComprehension
      (OrdinalCarrier ((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)) :
    ∃ A L, StableHartogsPresentation (@LowerNat σ _) A L :=
  stable_hartogs_presentation LowerNat rigidN (fun m n hm hn => lowerNat_nd hi m n hm hn)
    rcF rcR rcH rcL rcMap

#classicism_check stable_segment_rigid stable_index_presentation stable_hartogs_presentation natural_stable_hartogs_presentation
#classicism_types stable_segment_rigid stable_index_presentation stable_hartogs_presentation natural_stable_hartogs_presentation
end Classicism.MathematicalContingency
