import Classicism.Results.MathematicalContingency.HartogsSmallness
import Classicism.Results.MathematicalContingency.NaturalWellOrder

/-!
The natural seed and intended double-Hartogs carrier below an inaccessible.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
StronglyInaccessible uses LowerNat at the individual type e. This is why the
inaccessible corollaries specialize to e; no cross-type natural identification
or extra small-natural hypothesis is silently introduced.
-/
namespace Classicism.MathematicalContingency
variable {κ σ : Type} [Ty κ] [Ty σ]

theorem small_lowerNat_of_not_embeds (K : κ → Prop) (L : κ → κ → Prop)
    (hk : WellOrderOn K L) (hp : LowerPeano σ)
    (gap : ¬ Embeds K (@LowerNat σ _)) : Small K L (@LowerNat σ _) :=
  small_of_wellOrder_not_embeds K L LowerNat LowerLT hk (lowerNat_wellOrder hp) gap

theorem small_lowerNat_of_inaccessible (K : κ → Prop) (L : κ → κ → Prop)
    (inaccessible : StronglyInaccessible K L) (hp : LowerPeano e) :
    Small K L (@LowerNat e _) :=
  small_lowerNat_of_not_embeds K L inaccessible.1.1 hp inaccessible.2.1.2

theorem small_natural_doubleHartogs (K : κ → Prop) (L : κ → κ → Prop)
    (inaccessible : StronglyInaccessible K L) (hp : LowerPeano e)
    (rcK : P.RigidComprehension (κ → Prop))
    (rcN : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rc1 : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop)) :
    Small K L (HartogsCarrier (HartogsCarrier (@LowerNat e _))) :=
  small_doubleHartogs K L inaccessible.1.1 inaccessible.2.2.2 rcK LowerNat rcN rc1 rc2
    (small_lowerNat_of_inaccessible K L inaccessible hp)

#classicism_check small_lowerNat_of_not_embeds small_lowerNat_of_inaccessible small_natural_doubleHartogs
#classicism_types small_lowerNat_of_not_embeds small_lowerNat_of_inaccessible small_natural_doubleHartogs
end Classicism.MathematicalContingency
