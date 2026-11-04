import Classicism.Results.BourbakiWitt.Derive.ActualityCodeBasic

/-! A bounded batch of certificates, so later batches import checked derivations
instead of retaining all translation work in one compiler process. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.dl_le
  Classicism.Proofs.BWActuality.dl_disjoint
  Classicism.Proofs.BWActuality.wd_serial
  Classicism.Proofs.BWActuality.k2_child
  Classicism.Proofs.BWActuality.b_meet
