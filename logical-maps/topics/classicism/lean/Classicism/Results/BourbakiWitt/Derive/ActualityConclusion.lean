import Classicism.Results.BourbakiWitt.Derive.ActualityValue

/-! A bounded certificate batch; the mathematical proofs are unchanged. -/

set_option maxHeartbeats 0 in
#classicism_derive
  Classicism.Proofs.BWActuality.not_zd_contradiction
  Classicism.Proofs.BWActuality.vicinity_boolean_completeness_t_and_relational_choice_imply_actuality
