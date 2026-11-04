import Classicism.Results.BourbakiWitt.Derive.ActualityCodeTrue

/-! A bounded batch of certificates, so later batches import checked derivations
instead of retaining all translation work in one compiler process. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.g_eq
