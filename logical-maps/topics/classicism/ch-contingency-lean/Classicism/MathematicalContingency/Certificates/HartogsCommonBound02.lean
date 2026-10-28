import Diagnostics.DeepSplitCommonBound

/-! Re-export the separately kernel-checked certificate. Its generating source
and full axiom audit are preserved in the imported module. -/
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.doubleHartogs_commonPairedBound_nontrivial.derivable
