import Classicism.Results.BourbakiWitt.Derive.ActualityCodeFalse

/-! A bounded batch of certificates, so later batches import checked derivations
instead of retaining all translation work in one compiler process. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.h_holds
  Classicism.Proofs.BWActuality.hc_settled
