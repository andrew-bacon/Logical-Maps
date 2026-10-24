import Classicism.Results.Research.RigidityClosureResearchFinite
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema
import Classicism.Certified.Schemas

/-! Check requests, not an assertion they have passed. Missing tuple derivations
are deliberately compilation errors, so unary proofs cannot be presented as
full finite-arity certificates merely because their shallow forms compile. -/
#classicism_audit Classicism.Results.Research.RigidityClosureResearchFinite
#classicism_types_audit Classicism.Results.Research.RigidityClosureResearchFinite

#classicism_schema Classicism.Research.RigidityClosure.WeakMeetClosure
  Classicism.Research.RigidityClosure.RigidMeetClosure
  Classicism.Research.RigidityClosure.WeakDifferenceClosure
  Classicism.Research.RigidityClosure.RigidDifferenceClosure
  Classicism.Research.RigidityClosure.WeakComplementClosure
  Classicism.Research.RigidityClosure.RigidComplementClosure
  Classicism.Research.RigidityClosure.WeakSymmetricDifferenceClosure
  Classicism.Research.RigidityClosure.RigidSymmetricDifferenceClosure
  Classicism.Research.RigidityClosure.WeakBivalence
  Classicism.Research.RigidityClosure.RigidBivalence

#classicism_derive Classicism.Research.RigidityClosure.nd_seals_nonmembership
  Classicism.Research.RigidityClosure.weak_cut
  Classicism.Research.RigidityClosure.rigid_cut
  Classicism.Research.RigidityClosure.weak_union
  Classicism.Research.RigidityClosure.rigid_union
  Classicism.Research.RigidityClosure.weak_complement_iff_nd_barcan
  Classicism.Research.RigidityClosure.rigid_complement_iff_nd_necessary_barcan
  Classicism.Research.RigidityClosure.weak_complement_tt_iff_c5
  Classicism.Research.RigidityClosure.rigid_complement_tt_iff_c5

#classicism_certify Classicism.Research.RigidityClosure.nd_weak_meet
  Classicism.Research.RigidityClosure.nd_rigid_meet
  Classicism.Research.RigidityClosure.nd_weak_difference
  Classicism.Research.RigidityClosure.nd_rigid_difference
  Classicism.Research.RigidityClosure.nd_of_weak_meet
  Classicism.Research.RigidityClosure.nd_of_rigid_meet
  Classicism.Research.RigidityClosure.nd_of_weak_difference
  Classicism.Research.RigidityClosure.nd_of_rigid_difference
  Classicism.Research.RigidityClosure.nd_weak_symmetric_difference
  Classicism.Research.RigidityClosure.nd_rigid_symmetric_difference
  Classicism.Research.RigidityClosure.nd_of_weak_symmetric_difference
  Classicism.Research.RigidityClosure.nd_of_rigid_symmetric_difference
  Classicism.Research.RigidityClosure.nd_weak_bivalence
  Classicism.Research.RigidityClosure.nd_rigid_bivalence
  Classicism.Research.RigidityClosure.nd_of_weak_bivalence
  Classicism.Research.RigidityClosure.nd_of_rigid_bivalence

#check Classicism.Research.RigidityClosure.nd_rigid_meet.listRule
#check Classicism.Research.RigidityClosure.nd_of_rigid_meet.listRule
#check Classicism.Research.RigidityClosure.nd_rigid_difference.listRule
#check Classicism.Research.RigidityClosure.nd_of_rigid_difference.listRule
#print axioms Classicism.Research.RigidityClosure.rigid_cut.derivable
#print axioms Classicism.Research.RigidityClosure.nd_rigid_meet.listRule
#print axioms Classicism.Research.RigidityClosure.rigid_complement_tt_iff_c5.derivable
