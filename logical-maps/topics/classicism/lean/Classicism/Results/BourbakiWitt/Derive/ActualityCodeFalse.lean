import Classicism.Results.BourbakiWitt.Derive.ActualityCodeParts

/-! A bounded batch of certificates, so later batches import checked derivations
instead of retaining all translation work in one compiler process. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.h_fails_chosen
  Classicism.Proofs.BWActuality.h_fails_other
  Classicism.Proofs.BWActuality.h_fails_at
  Classicism.Proofs.BWActuality.h_fails
