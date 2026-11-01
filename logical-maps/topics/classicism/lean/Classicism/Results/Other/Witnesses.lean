import Classicism.Results.Other.Meta
import Classicism.Certified.Entailed

/-!
# Witnesses: failures in Lean models, through the map's results (1 November 2026)

A failure of a principle in a Lean model, obtained from the model's certified verdicts by the
map's certified results, read semantically (`Premodel.entails_holds`, soundness): if `X ∪ Y ⟹ Z`,
`Y` holds in a model and `Z` fails there, `X` fails there. Each failure makes the negation of a
failing instance consistent with `C` (`consistent_neg_of_not_holdsAx`), which is what the
incompatibilities with Maximalism need (`maximalist_box_inconsistent_of_model`).

- **Truths are 5-necessary** and **Truths are two-hat necessary** fail in the full model on the
  two-element group (`full-involution-group`): `□ND` gives `□(□̂̂ ⇒ □_≠)`, hence `□̂̂ ⇒ □_≠`;
  `□`Rigid Comprehension gives Actuality, hence `□₅ ⇒ □̂̂`; so `□₅ ⇒ □_≠`, and with
  `p ⇒ □₅p` the Distinctness-Preserving Collapse would hold, which fails there.
- **Two-hat necessity implies ND-necessity** and **5-necessity implies ND-necessity** fail in the
  full two-object model with two retractions (`full-two-object-double-retraction`): Actuality holds
  there (from `□`Rigid Comprehension), and with `□̂̂ ⇒ □_≠` it gives Strong Actuality, which fails.
- **Weakly Inextensible Comprehension** fails in the truncation model (Appendix D, Part 6,
  `finite-support-truncations`): Atomicity at `t` holds there, Actuality fails, and the two give
  Actuality (`atomicity-t-and-weakly-inextensible-comprehension-imply-actuality`).
- **Tame Rigidity** fails in the two-object model after Part 8 (`finite-support-two-object-all-maps`):
  BF holds there and `□BF` fails (`tame-rigidity-and-barcan-imply-necessary-barcan`).
-/

namespace Classicism.Meta

open AxiomSet Intensional

namespace Witness

variable {C : Type} [CategoryTheory.SmallCategory C] {B : Premodel Signature.pure C}

/-! ### Soundness of the map's results, in a model -/

theorem holds₁ (M : B.IsModel) {X Z : AxiomSet Signature.pure} (e : X ⟹ Z) (h : B.HoldsAx X) :
    B.HoldsAx Z :=
  B.entails_holds M e h

theorem holds₂ (M : B.IsModel) {X Y Z : AxiomSet Signature.pure} (e : X ∪ Y ⟹ Z) (hX : B.HoldsAx X)
    (hY : B.HoldsAx Y) : B.HoldsAx Z :=
  B.entails_holds M e (Premodel.holdsAx_union B hX hY)

theorem not_holds₁ (M : B.IsModel) {X Z : AxiomSet Signature.pure} (e : X ⟹ Z) (hZ : ¬ B.HoldsAx Z) :
    ¬ B.HoldsAx X := fun h => hZ (holds₁ M e h)

theorem not_holds_left (M : B.IsModel) {X Y Z : AxiomSet Signature.pure} (e : X ∪ Y ⟹ Z)
    (hY : B.HoldsAx Y) (hZ : ¬ B.HoldsAx Z) : ¬ B.HoldsAx X := fun h => hZ (holds₂ M e h hY)

theorem not_holds_right (M : B.IsModel) {X Y Z : AxiomSet Signature.pure} (e : X ∪ Y ⟹ Z)
    (hX : B.HoldsAx X) (hZ : ¬ B.HoldsAx Z) : ¬ B.HoldsAx Y := fun h => hZ (holds₂ M e hX h)

/-- A schema failing in a model has an instance whose negation is consistent with `C`. -/
theorem exists_consistent_neg_of_not_holdsAx (M : B.IsModel) {X : AxiomSet Signature.pure}
    (h : ¬ B.HoldsAx X) : ∃ p, X p ∧ ¬ B.HoldsSentence p ∧ Consistent (single (Term.neg p)) := by
  by_contra hn
  refine h fun p hp => Classical.byContradiction fun hq => hn ⟨p, hp, hq, ?_⟩
  exact Consistent.of_model B M (Premodel.holdsAx_single B ((B.holdsSentence_neg M p).2 hq))

/-- A sentence failing in a model has a negation consistent with `C`. -/
theorem consistent_neg_of_not_holds (M : B.IsModel) {q : Sentence Signature.pure}
    (h : ¬ B.HoldsSentence q) : Consistent (single (Term.neg q)) :=
  Consistent.of_model B M (Premodel.holdsAx_single B ((B.holdsSentence_neg M q).2 h))

/-- A model of the map's verdict statement, read in the pure language. -/
theorem pure_of {X : AxiomSet Signature.pure} (h : B.HoldsAx (AxiomSet.ofPure X)) : B.HoldsAx X :=
  (Premodel.holdsAx_schemaIn_iff B X).1 h

end Witness

open Witness

/-! ### The full model on the two-element group -/

namespace Invol

local notation "A" => MSet.model Intensional.Invol
local notation "M" => MSet.model_isModel Intensional.Invol

theorem holdsAx_twoHatImpliesNd : (A).HoldsAx P.TwoHatImpliesNdNecessity.schema :=
  holds₁ M Proofs.necessary_two_hat_implies_nd_necessity_implies_two_hat_implies_nd_necessity.entails
    (holds₁ M Proofs.necessary_distinctness_necessary_t_implies_necessary_two_hat_implies_nd.entails
      (holds₁ M Proofs.necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t.entails
        (pure_of Map.Models.full_involution_group.necessary_distinctness_necessary_r.2)))

theorem holdsAx_actuality : (A).HoldsAx P.Actuality.schema :=
  holds₁ M Proofs.rigid_comprehension_r_implies_actuality.entails
    (holds₁ M Proofs.necessary_rigid_comprehension_r_implies_rigid_comprehension_r.entails
      (pure_of Map.Models.full_involution_group.necessary_rigid_comprehension_r.2))

theorem holdsAx_fiveImpliesNd : (A).HoldsAx P.FiveImpliesNdNecessity.schema :=
  holds₂ M Proofs.two_hat_implies_nd_and_five_implies_two_hat_imply_five_implies_nd.entails
    holdsAx_twoHatImpliesNd (holds₁ M Proofs.actuality_implies_five_implies_two_hat.entails holdsAx_actuality)

/-- **Truths are 5-necessary fails** in the full model on the two-element group. -/
theorem not_truthImpliesFive : ¬ (A).HoldsAx P.TruthImpliesFiveNecessity.schema :=
  not_holds_right M Proofs.five_implies_nd_and_truth_implies_five_imply_truth_implies_nd.entails
    holdsAx_fiveImpliesNd (fun h => Map.Models.full_involution_group.distinctness_preserving_collapse.2
      ((Premodel.holdsAx_schemaIn_iff _ _).2 h))

/-- **Truths are two-hat necessary fails** there too. -/
theorem not_truthImpliesTwoHat : ¬ (A).HoldsAx P.TruthImpliesTwoHatNecessity.schema :=
  not_holds₁ M Proofs.truth_implies_two_hat_implies_truth_implies_five.entails not_truthImpliesFive

end Invol

/-! ### The full two-object model with two retractions -/

namespace DoubleRetraction

local notation "A" => FullActionModels.doubleRetraction
local notation "M" => FullActionModels.unitModel_isModel FullActionModels.DRObj.w0

theorem holdsAx_actuality : (A).HoldsAx P.Actuality.schema :=
  holds₁ M Proofs.rigid_comprehension_r_implies_actuality.entails
    (holds₁ M Proofs.necessary_rigid_comprehension_r_implies_rigid_comprehension_r.entails
      (pure_of Map.Models.full_two_object_double_retraction.necessary_rigid_comprehension_r.2))

/-- **Two-hat necessity implies ND-necessity fails** in the full two-object model with two
retractions: with Actuality it would give Strong Actuality. -/
theorem not_twoHatImpliesNd : ¬ (A).HoldsAx P.TwoHatImpliesNdNecessity.schema :=
  not_holds_right M Proofs.actuality_and_two_hat_implies_nd_imply_strong_actuality.entails
    holdsAx_actuality (fun h => Map.Models.full_two_object_double_retraction.strong_actuality.2
      ((Premodel.holdsAx_schemaIn_iff _ _).2 h))

/-- **5-necessity implies ND-necessity fails** there too. -/
theorem not_fiveImpliesNd : ¬ (A).HoldsAx P.FiveImpliesNdNecessity.schema :=
  not_holds₁ M Proofs.five_implies_nd_implies_two_hat_implies_nd.entails not_twoHatImpliesNd

end DoubleRetraction

/-! ### The truncation model (Appendix D, Part 6) -/

namespace Truncs

local notation "A" => MonoidModel.model Monoids.truncs
local notation "M" => MonoidModel.model_isModel Monoids.truncs

/-- **Weakly Inextensible Comprehension fails** in the truncation model: with Atomicity at `t`
it gives Actuality, which fails. -/
theorem not_weaklyInextensibleComprehension :
    ¬ (A).HoldsAx P.WeaklyInextensibleComprehension.schema :=
  not_holds_right M Proofs.atomicity_t_and_weakly_inextensible_comprehension_imply_actuality.entails
    (Premodel.holdsAx_single _ Monoids.Truncs.atomicityT)
    (fun h => Monoids.Truncs.not_actuality (h _ rfl))

end Truncs

/-! ### The two-object model after Part 8 -/

namespace ContingentBarcan

local notation "A" => Intensional.ContingentBarcan.model
local notation "M" => Intensional.ContingentBarcan.model_isModel

/-- **Tame Rigidity fails** in the two-object model after Part 8: with BF it gives `□BF`. -/
theorem not_tameRigidity : ¬ (A).HoldsAx P.TameRigidity.schema :=
  not_holds_left M Proofs.tame_rigidity_and_barcan_imply_necessary_barcan.entails
    (pure_of Map.Models.finite_support_two_object_all_maps.barcan_r.2)
    (fun h => Map.Models.finite_support_two_object_all_maps.necessary_barcan_r.2
      ((Premodel.holdsAx_schemaIn_iff _ _).2 h))

end ContingentBarcan

/-! ### Maximalism against the necessitations

`maximalist_box_inconsistent_of_model` at each failure above. -/

/-- `maximalist-distinctness-incompatible-with-necessary-truth-implies-five-necessity`. -/
theorem maximalist_necTruthImpliesFive_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecTruthImpliesFiveNecessity.schema) :=
  maximalist_box_inconsistent_of_model _ (MSet.model_isModel Intensional.Invol)
    P.TruthImpliesFiveNecessity.schema_closedTypes Invol.not_truthImpliesFive
    (by rintro _ ⟨_, rfl, rfl⟩; rfl)

/-- `maximalist-distinctness-incompatible-with-necessary-truth-implies-two-hat-necessity`. -/
theorem maximalist_necTruthImpliesTwoHat_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecTruthImpliesTwoHatNecessity.schema) :=
  maximalist_box_inconsistent_of_model _ (MSet.model_isModel Intensional.Invol)
    P.TruthImpliesTwoHatNecessity.schema_closedTypes Invol.not_truthImpliesTwoHat
    (by rintro _ ⟨_, rfl, rfl⟩; rfl)

/-- `maximalist-distinctness-incompatible-with-necessary-two-hat-implies-nd-necessity`. -/
theorem maximalist_necTwoHatImpliesNd_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecTwoHatImpliesNdNecessity.schema) :=
  maximalist_box_inconsistent_of_model _ (FullActionModels.unitModel_isModel FullActionModels.DRObj.w0)
    P.TwoHatImpliesNdNecessity.schema_closedTypes DoubleRetraction.not_twoHatImpliesNd
    (by rintro _ ⟨_, rfl, rfl⟩; rfl)

/-- `maximalist-distinctness-incompatible-with-necessary-five-implies-nd-necessity`. -/
theorem maximalist_necFiveImpliesNd_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecFiveImpliesNdNecessity.schema) :=
  maximalist_box_inconsistent_of_model _ (FullActionModels.unitModel_isModel FullActionModels.DRObj.w0)
    P.FiveImpliesNdNecessity.schema_closedTypes DoubleRetraction.not_fiveImpliesNd
    (by rintro _ ⟨_, rfl, rfl⟩; rfl)

/-- `maximalist-distinctness-incompatible-with-necessary-weakly-inextensible-comprehension-r`. -/
theorem maximalist_necWeaklyInextensibleComprehension_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecWeaklyInextensibleComprehension.schema) :=
  maximalist_box_inconsistent_of_model _ (MonoidModel.model_isModel Monoids.truncs)
    P.WeaklyInextensibleComprehension.schema_closedTypes Truncs.not_weaklyInextensibleComprehension
    (by rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩; exact ⟨τ, hτ, rfl⟩)

/-- `maximalist-distinctness-incompatible-with-necessary-tame-rigidity-r`. -/
theorem maximalist_necTameRigidity_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecTameRigidity.schema) :=
  maximalist_box_inconsistent_of_model _ Intensional.ContingentBarcan.model_isModel
    P.TameRigidity.schema_closedTypes ContingentBarcan.not_tameRigidity
    (by rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩; exact ⟨τ, hτ, rfl⟩)

end Classicism.Meta
