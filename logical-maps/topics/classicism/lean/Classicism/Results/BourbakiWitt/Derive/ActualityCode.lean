import Classicism.Results.BourbakiWitt.Derive.ActualityCodeStep

/-! Audit every theorem of ActualityCode after compiling its derivations in
small dependency-ordered batches. The mathematical proofs are unchanged. -/
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.BourbakiWitt.ActualityCode
