import Classicism.Results.MathematicalContingency.CountableRowSurjection
import Classicism.Results.MathematicalContingency.WellOrderSurjection

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

theorem stableIndex_possible_orderTypeCH
    (N : σ → Prop) (H I : τ → Prop) (R LI : τ → τ → Prop)
    (stable : StableIndexPresentation N H I R LI)
    (rcN : □ (P.RigidComprehension (σ → Prop)))
    (rcH : □ (P.RigidComprehension (OrdinalCarrier σ → Prop)))
    (surjection : ◇ (∃ F, Surjects F I (RigidPower N))) :
    ◇ (Equinumerous (RigidPower N) (HartogsCarrier N)) :=
  possible_rigidPower_equinumerous_hartogs_of_possible_surjects N I LI rcN rcH
    stable.2.2.2.2.2.1 stable.2.2.2.2.2.2.2 surjection

#classicism_check stableIndex_possible_orderTypeCH
#classicism_types stableIndex_possible_orderTypeCH
end Classicism.MathematicalContingency
