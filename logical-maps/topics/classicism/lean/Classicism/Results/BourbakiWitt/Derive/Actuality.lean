import Classicism.Results.BourbakiWitt.Derive.ActualityConclusion

/-! Audit every theorem after compiling its certificates in small batches. -/
set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.BourbakiWitt.Actuality
