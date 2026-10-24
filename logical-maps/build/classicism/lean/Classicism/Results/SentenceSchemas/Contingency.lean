import Classicism.Certified.Schemas
import Classicism.Syntax.SentenceSchemas
import Classicism.Syntax.Pure

/-!
# No Pure Contingency, No Contingency, and B for sentences

The arrows among the map's contingency schemas and out of them:

- **No Pure Contingency carries any pure principle to its boxed form** — the uniform
  family `no-pure-contingency-and-X-imply-necessary-X` (BF, ND, Atomicity, Fregean,
  five, B, Vicinity, Transversal, …, twenty-four records). A boxed principle says that each closed instance of the
  base is necessary, and No Pure Contingency says exactly that of a true pure sentence.
  Here it is one theorem, `npc_union_entails_box`: for any schema `Ax` of pure sentences,
  `NPC ∪ Ax ⟹ Ax.box`; in the pure signature every schema is pure, so every record of
  the family is an instance, and the two boxed principles the shallow layer states,
  `□BF_t` and `□ND_t`, are named.
- `no-contingency-signature-r-implies-no-pure-contingency-r`,
  `signature-b-r-implies-pure-b-r`: restrictions of a schema to its pure instances.
- `no-contingency-signature-r-implies-signature-b-r`, `no-pure-contingency-r-implies-pure-b-r`:
  from `P → □P` and the necessitation of `P → ◇P`, `K` gives `P → □◇P`. The one
  object-level step, `imp_box_imp_box_dia`, is a shallow lemma certified once.
- `modal-b-implies-signature-b-r`: B instantiated at the proposition a closed sentence
  expresses — `allEβ` at the sentence.
- `fregean-axiom-implies-no-contingency-signature-r` and `-no-pure-contingency-r`: under
  the Fregean Axiom a true sentence is identical to `⊤`; the shallow lemma `fregean_box`.
- `possible-infinity-e-and-no-pure-contingency-imply-axiom-of-infinity-e`, and at `t`: the
  Axiom of Infinity is a pure sentence, so No Pure Contingency at its negation and its
  possibility make it true; the shallow lemma `npc_dia_imp`.

Each is stated for any signature `Sig`; the map's type-indexed principles at a signature
are their pure schemas read there, `P.schema.ofPure`.
-/

namespace Classicism

/-- Under the Fregean Axiom, what is true is necessary: `p ↔ ⊤`, so `p = ⊤`. -/
theorem fregean_box (p : Prop) : P.FregeanAxiom → p → □ p :=
  fun hF hp => hF p True ⟨fun _ => trivial, fun _ => hp⟩

/-- From `p → □p`, `p → □◇p`: necessitate `p → ◇p` and apply `K`. -/
theorem imp_box_imp_box_dia (p : Prop) : (p → □ p) → p → □ ◇ p :=
  fun h hp => modal_K _ _ (nec% (dia_intro p)) (h hp)

/-- A possible proposition that is not contingently false is true: from `¬p → □¬p` and
`◇p`, `p`. -/
theorem npc_dia_imp (p : Prop) : (¬ p → □ ¬ p) → ◇ p → p :=
  fun h hd => (em p).elim id fun hn => absurd hd (not_dia_of_box_not p (h hn))

#classicism_derive Classicism.fregean_box Classicism.imp_box_imp_box_dia Classicism.npc_dia_imp

namespace Meta

open AxiomSet

variable {Sig : Signature}

/-! ### No Pure Contingency necessitates every pure principle -/

/-- **No Pure Contingency with a schema of pure sentences entails its necessitation.**
The map's family `no-pure-contingency-and-X-imply-necessary-X`, for every `X`. -/
theorem npc_union_entails_box {Ax : AxiomSet Sig} (hP : Pure Ax) (hC : ClosedTypes Ax) :
    npc Sig ∪ Ax ⟹ Ax.box := by
  rintro a ⟨p, hp, rfl⟩
  exact (Theorem.ax (Or.inl ⟨by simpa using hC p hp, p, hP p hp, rfl⟩)).mp (Theorem.ax (Or.inr hp))

/-- No Contingency for the signature necessitates every schema, pure or not. -/
theorem noContingency_union_entails_box {Ax : AxiomSet Sig} (hC : ClosedTypes Ax) :
    noContingency Sig ∪ Ax ⟹ Ax.box := by
  rintro a ⟨p, hp, rfl⟩
  exact (Theorem.ax (Or.inl ⟨by simpa using hC p hp, p, rfl⟩)).mp (Theorem.ax (Or.inr hp))

/-- In the pure signature, where the map's principles live, every schema is pure; a schema
of a principle is in the paper's language (`P.X.schema_closedTypes`). -/
theorem npc_union_entails_box_pure {Ax : AxiomSet Signature.pure} (hC : ClosedTypes Ax) :
    npc Signature.pure ∪ Ax ⟹ Ax.box :=
  npc_union_entails_box (Pure.of_pureSig Ax) hC

/-- `no-pure-contingency-and-bf-t-imply-necessary-bf-t`. -/
theorem npc_barcanT_entails_necBarcanT :
    npc Signature.pure ∪ P.BarcanT.schema ⟹ P.NecBarcanT.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.BarcanT.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-nd-t-imply-necessary-nd-t`. -/
theorem npc_ndT_entails_necNdT :
    npc Signature.pure ∪ P.NecessityOfDistinctnessT.schema ⟹ P.NecNecessityOfDistinctnessT.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.NecessityOfDistinctnessT.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-bf-imply-necessary-bf`, at every type. -/
theorem npc_barcan_entails_box : npc Signature.pure ∪ P.Barcan.schema ⟹ AxiomSet.box P.Barcan.schema :=
  npc_union_entails_box_pure P.Barcan.schema_closedTypes

/-- `no-pure-contingency-and-nd-imply-necessary-nd`, at every type. -/
theorem npc_nd_entails_box :
    npc Signature.pure ∪ P.NecessityOfDistinctness.schema ⟹ AxiomSet.box P.NecessityOfDistinctness.schema :=
  npc_union_entails_box_pure P.NecessityOfDistinctness.schema_closedTypes

/-- `no-pure-contingency-and-vicinity-imply-necessary-vicinity`. -/
theorem npc_vicinity_entails_necVicinity :
    npc Signature.pure ∪ P.Vicinity.schema ⟹ P.NecVicinity.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.Vicinity.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-strong-actuality-imply-necessary-strong-actuality`. -/
theorem npc_strongActuality_entails_necStrongActuality :
    npc Signature.pure ∪ P.StrongActuality.schema ⟹ P.NecStrongActuality.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.StrongActuality.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-transversal-imply-necessary-transversal`. -/
theorem npc_transversal_entails_necTransversal :
    npc Signature.pure ∪ P.Transversal.schema ⟹ P.NecTransversal.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  exact npc_union_entails_box_pure P.Transversal.schema_closedTypes _ (AxiomSet.mem_box ⟨σ, hσ, rfl⟩)

/-- `no-pure-contingency-and-transversal-choice-imply-necessary-transversal-choice`. -/
theorem npc_transversalChoice_entails_necTransversalChoice :
    npc Signature.pure ∪ P.TransversalChoice.schema ⟹ P.NecTransversalChoice.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  exact npc_union_entails_box_pure P.TransversalChoice.schema_closedTypes _ (AxiomSet.mem_box ⟨σ, hσ, rfl⟩)

/-- `no-pure-contingency-and-weakly-inextensible-comprehension-imply-necessary-weakly-inextensible-comprehension`. -/
theorem npc_weaklyInextensibleComprehension_entails_box :
    npc Signature.pure ∪ P.WeaklyInextensibleComprehension.schema ⟹
      P.NecWeaklyInextensibleComprehension.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  exact npc_union_entails_box_pure P.WeaklyInextensibleComprehension.schema_closedTypes _
    (AxiomSet.mem_box ⟨ρ, hρ, rfl⟩)

/-- `no-pure-contingency-and-actuality-imply-necessary-actuality`. -/
theorem npc_actuality_entails_necActuality :
    npc Signature.pure ∪ P.Actuality.schema ⟹ P.NecActuality.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.Actuality.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-completeness-imply-necessary-completeness`, at every type. -/
theorem npc_booleanCompleteness_entails_box :
    npc Signature.pure ∪ P.BooleanCompleteness.schema ⟹ AxiomSet.box P.BooleanCompleteness.schema :=
  npc_union_entails_box_pure P.BooleanCompleteness.schema_closedTypes

/-- `no-pure-contingency-and-atomicity-imply-necessary-atomicity`, at every type. -/
theorem npc_atomicity_entails_box :
    npc Signature.pure ∪ P.Atomicity.schema ⟹ AxiomSet.box P.Atomicity.schema :=
  npc_union_entails_box_pure P.Atomicity.schema_closedTypes

/-- `no-pure-contingency-and-fregean-imply-necessary-fregean`. -/
theorem npc_fregean_entails_box :
    npc Signature.pure ∪ P.FregeanAxiom.schema ⟹ AxiomSet.box P.FregeanAxiom.schema :=
  npc_union_entails_box_pure P.FregeanAxiom.schema_closedTypes

/-! ### The varieties of necessity (20 October 2026) -/

/-- `no-pure-contingency-and-truth-implies-five-necessity-imply-necessary-truth-implies-five-necessity`. -/
theorem npc_truthImpliesFive_entails_nec :
    npc Signature.pure ∪ P.TruthImpliesFiveNecessity.schema ⟹ P.NecTruthImpliesFiveNecessity.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.TruthImpliesFiveNecessity.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-truth-implies-two-hat-necessity-imply-necessary-truth-implies-two-hat-necessity`. -/
theorem npc_truthImpliesTwoHat_entails_nec :
    npc Signature.pure ∪ P.TruthImpliesTwoHatNecessity.schema ⟹ P.NecTruthImpliesTwoHatNecessity.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.TruthImpliesTwoHatNecessity.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-five-implies-two-hat-necessity-imply-necessary-five-implies-two-hat-necessity`. -/
theorem npc_fiveImpliesTwoHat_entails_nec :
    npc Signature.pure ∪ P.FiveImpliesTwoHatNecessity.schema ⟹ P.NecFiveImpliesTwoHatNecessity.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.FiveImpliesTwoHatNecessity.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-five-implies-nd-necessity-imply-necessary-five-implies-nd-necessity`. -/
theorem npc_fiveImpliesNd_entails_nec :
    npc Signature.pure ∪ P.FiveImpliesNdNecessity.schema ⟹ P.NecFiveImpliesNdNecessity.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.FiveImpliesNdNecessity.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-two-hat-implies-nd-necessity-imply-necessary-two-hat-implies-nd-necessity`. -/
theorem npc_twoHatImpliesNd_entails_nec :
    npc Signature.pure ∪ P.TwoHatImpliesNdNecessity.schema ⟹ P.NecTwoHatImpliesNdNecessity.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.TwoHatImpliesNdNecessity.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-! ### Restrictions -/

/-- `no-contingency-signature-r-implies-no-pure-contingency-r`. -/
theorem noContingency_entails_npc : noContingency Sig ⟹ npc Sig :=
  Entails.of_subset npc_subset_noContingency

/-- `signature-b-r-implies-pure-b-r`. -/
theorem signatureB_entails_pureB : signatureB Sig ⟹ pureB Sig :=
  Entails.of_subset pureB_subset_signatureB

/-! ### From `P → □P` to `P → □◇P` -/

/-- `no-contingency-signature-r-implies-signature-b-r`. -/
theorem noContingency_entails_signatureB : noContingency Sig ⟹ signatureB Sig := by
  rintro a ⟨hc, p, rfl⟩
  exact Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure imp_box_imp_box_dia.derivable)) p)
    (Theorem.ax ⟨by simpa using hc, p, rfl⟩)

/-- `no-pure-contingency-r-implies-pure-b-r`. -/
theorem npc_entails_pureB : npc Sig ⟹ pureB Sig := by
  rintro a ⟨hc, p, hp, rfl⟩
  exact Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure imp_box_imp_box_dia.derivable)) p)
    (Theorem.ax ⟨by simpa using hc, p, hp, rfl⟩)

/-! ### B and the Fregean Axiom -/

/-- `modal-b-implies-signature-b-r`: B at the proposition the sentence expresses. -/
theorem modalB_entails_signatureB : AxiomSet.ofPure P.ModalB.schema ⟹ signatureB Sig := by
  rintro a ⟨-, p, rfl⟩
  exact Derivable.allEβ
    (Theorem.ax (AxiomSet.mem_ofPure (Ax := P.ModalB.schema) (p := P.ModalB.quoted) rfl)) p

/-- `fregean-axiom-implies-no-contingency-signature-r`. -/
theorem fregean_entails_noContingency : AxiomSet.ofPure P.FregeanAxiom.schema ⟹ noContingency Sig := by
  rintro a ⟨-, p, rfl⟩
  exact Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure fregean_box.derivable)) p)
    (Theorem.ax (AxiomSet.mem_ofPure (Ax := P.FregeanAxiom.schema) (p := P.FregeanAxiom.quoted) rfl))

/-- `fregean-axiom-implies-no-pure-contingency-r`. -/
theorem fregean_entails_npc : AxiomSet.ofPure P.FregeanAxiom.schema ⟹ npc Sig :=
  Entails.trans fregean_entails_noContingency noContingency_entails_npc

/-- The same two in the pure signature, where the schema is the map's principle itself. -/
theorem fregean_entails_npc_pure : P.FregeanAxiom.schema ⟹ npc Signature.pure := by
  rintro a ⟨-, p, hp, rfl⟩
  exact Theorem.mp (Derivable.allEβ (Theorem.ofCMinus fregean_box.derivable) p)
    (Theorem.ax (Ax := P.FregeanAxiom.schema) (a := P.FregeanAxiom.quoted) rfl)

/-- `possible-infinity-e-and-no-pure-contingency-imply-axiom-of-infinity-e`: the Axiom of
Infinity at `e` is pure, so No Pure Contingency makes its negation necessary if true,
against its possibility. -/
theorem npc_possibleInfinityE_entails_axiomOfInfinityE :
    npc Signature.pure ∪ P.PossibleInfinityE.schema ⟹ P.AxiomOfInfinityE.schema := by
  rintro a rfl
  exact Theorem.mp₂ (Derivable.allEβ (Theorem.ofCMinus npc_dia_imp.derivable) P.AxiomOfInfinityE.quoted)
    (Theorem.ax (Or.inl ⟨rfl, _, Term.pure_of_pureSig _, rfl⟩)) (Theorem.ax (Or.inr rfl))

/-- `possible-infinity-t-and-no-pure-contingency-imply-axiom-of-infinity-t`, likewise. -/
theorem npc_possibleInfinityT_entails_axiomOfInfinityT :
    npc Signature.pure ∪ P.PossibleInfinityT.schema ⟹ P.AxiomOfInfinityT.schema := by
  rintro a rfl
  exact Theorem.mp₂ (Derivable.allEβ (Theorem.ofCMinus npc_dia_imp.derivable) P.AxiomOfInfinityT.quoted)
    (Theorem.ax (Or.inl ⟨rfl, _, Term.pure_of_pureSig _, rfl⟩)) (Theorem.ax (Or.inr rfl))

/-- `modal-b-implies-pure-b-r`: B gives B for every pure sentence, in the pure language. -/
theorem modalB_entails_pureB : P.ModalB.schema ⟹ pureB Signature.pure := by
  rintro a ⟨-, p, hp, rfl⟩
  exact Derivable.allEβ (Theorem.ax (Ax := P.ModalB.schema) (a := P.ModalB.quoted) rfl) p

end Meta

end Classicism
