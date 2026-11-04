import Classicism.Results.BourbakiWitt.Derive.ActualityChain
import Classicism.Results.BourbakiWitt.ActualityCode
import Classicism.Tools.Translate
import Classicism.Certified.Schemas

/-! A bounded batch of certificates, so later batches import checked derivations
instead of retaining all translation work in one compiler process. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.disj_below
  Classicism.Proofs.BWActuality.le_of_and_neg_false
  Classicism.Proofs.BWActuality.and_neg_false_of_le
  Classicism.Proofs.BWActuality.xa_settled
  Classicism.Proofs.BWActuality.ge_settled
