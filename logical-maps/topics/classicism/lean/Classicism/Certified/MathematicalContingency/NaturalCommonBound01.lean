import Classicism.Certified.MathematicalContingency.NaturalCommonBound

/-! Re-export the separately kernel-checked certificate. Its generating source
and full axiom audit are preserved in the imported module. -/
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.natural_small_commonPairedBound.derivable
