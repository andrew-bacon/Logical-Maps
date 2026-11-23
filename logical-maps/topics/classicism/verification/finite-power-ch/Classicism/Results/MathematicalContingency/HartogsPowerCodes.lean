import Classicism.Results.MathematicalContingency.PairedRelationCoding
import Classicism.Results.MathematicalContingency.HartogsRanks
import Classicism.Results.MathematicalContingency.RigidImageCoding

/-! A realized Hartogs carrier embeds into two rigid powers of a paired carrier.
Code all realizations, without selecting representatives or collapsing H to
extensions of actual orders. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def HartogsRealizationCode (A : σ → Prop) (Q : σ → σ → σ → Prop)
    (a : OrdinalCarrier σ) (U : σ → Prop) : Prop :=
  RigidPower A U ∧ ∃ B R, (∀ x, B x → A x) ∧ WellOrderOn B R ∧
    ExactOrdinal a R B ∧ ∀ z, PairedBinaryImage Q (ReflexiveOrderGraph B R) z ↔ U z

theorem hartogsRealizationCode_exists (A : σ → Prop) (Q : σ → σ → σ → Prop)
    (hq : PairingOn A Q) (rc : P.RigidComprehension (σ → Prop))
    (a : OrdinalCarrier σ) (ha : HartogsCarrier A a) :
    ∃ U, HartogsRealizationCode A Q a U := by
  obtain ⟨R,B,sub,hw,he⟩ := ha.2
  obtain ⟨U,rigid,coext⟩ := rc (PairedBinaryImage Q (ReflexiveOrderGraph B R))
  refine ⟨U,⟨rigid,?_⟩,B,R,sub,hw,he,coext⟩
  intro z hz
  obtain ⟨x,y,_,hqz⟩ := (coext z).mpr hz
  exact (hq.1 x y z hqz).2.2

theorem hartogsRealizationCode_unique (A : σ → Prop) (Q : σ → σ → σ → Prop)
    (hq : PairingOn A Q) (a b : OrdinalCarrier σ) (ha : Ordinal a) (hb : Ordinal b)
    (U : σ → Prop) (hU : HartogsRealizationCode A Q a U)
    (kU : HartogsRealizationCode A Q b U) : a = b := by
  obtain ⟨_,B,R,subB,hw,he,codeB⟩ := hU
  obtain ⟨_,D,S,subD,hs,ke,codeD⟩ := kU
  have iso := pairedReflexiveOrder_iso A B D Q R S hq subB subD hw hs
    (fun z => (codeB z).trans (codeD z).symm)
  have transferred := (exactOrdinal_iso a ha B D R S _ hw hs iso).mp he
  exact exact_ordinal_unique a b ha hb D S transferred ke

theorem hartogs_embeds_twoRigidPowers (A : σ → Prop) (Q : σ → σ → σ → Prop)
    (hq : PairingOn A Q) (rc : P.RigidComprehension (σ → Prop))
    (rcPower : P.RigidComprehension ((σ → Prop) → Prop)) :
    Embeds (HartogsCarrier A) (RigidPower (RigidPower A)) := by
  apply rigidImageCode_embeds (RigidPower A) (RigidPower A) (HartogsCarrier A)
    (HartogsRealizationCode A Q) rcPower (embeds_refl (RigidPower A))
  · intro a _ U hU
    exact hU.1
  · intro a b ha hb coext
    obtain ⟨U,hU⟩ := hartogsRealizationCode_exists A Q hq rc a ha
    exact hartogsRealizationCode_unique A Q hq a b ha.1 hb.1 U hU ((coext U).mp hU)

#classicism_check hartogsRealizationCode_exists hartogsRealizationCode_unique hartogs_embeds_twoRigidPowers
#classicism_types hartogsRealizationCode_exists hartogsRealizationCode_unique hartogs_embeds_twoRigidPowers
end Classicism.MathematicalContingency
