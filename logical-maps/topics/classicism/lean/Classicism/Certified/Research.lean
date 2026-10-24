import Classicism.Results.Research.ChoiceActualityCertificates
import Classicism.Results.Research.InextensibleWeakPowerCertificates
import Classicism.Certified.Schemas

/-!
# Research results certified as entailments

Results proved in `Results/Research/` (ported 24 October 2026 from Daniel Kodsi's submission;
proofs by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi), read as entailments between schemas.
-/

#classicism_entails Classicism.Research.Choice.choice_completeness_actuality_sharp
#classicism_entails Classicism.Research.InextensiblePower.nd_ic_weaklyRigidPower

#check @Classicism.Research.Choice.choice_completeness_actuality_sharp.entails
#check @Classicism.Research.InextensiblePower.nd_ic_weaklyRigidPower.listEntails
