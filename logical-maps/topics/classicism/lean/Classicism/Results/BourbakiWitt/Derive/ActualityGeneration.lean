import Classicism.Results.BourbakiWitt.Derive.ActualityCode
import Classicism.Results.BourbakiWitt.Actuality
import Classicism.Tools.Translate
import Classicism.Certified.Schemas

/-! A bounded certificate batch; the mathematical proofs are unchanged. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.gen_tn_settled
  Classicism.Proofs.BWActuality.gen_tn_closed
  Classicism.Proofs.BWActuality.gen_tn_total
