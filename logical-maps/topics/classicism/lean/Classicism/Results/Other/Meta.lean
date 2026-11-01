import Classicism.Results.SentenceSchemas.Incompatibilities
import Classicism.Coalesced.Complete
import Classicism.MapDerived
import Classicism.Results.Other.Certificates

/-!
# Further results about the sentence schemas (1 November 2026)

- No Pure Contingency necessitates Atomlessness and Well-Ordering, as every pure principle
  (`npc_union_entails_box_pure`).
- **Maximalism excludes the necessitation of anything a model refutes**
  (`maximalist_box_inconsistent_of_model`): the model makes the negation of a failing instance
  consistent, and `max_box_inconsistent` applies. Its instances: `□`Atomlessness (it fails in
  `Prop`, whose one proposition `⊤` other than `⊥` is an atom), `□`Relational Choice (it fails
  in the symmetric model on all surjections, `symmetric-all-surjections`).
- `possibility-schema-r-implies-possible-infinity-t`: the Axiom of Infinity at `t` holds in the
  coalesced sum `coalesced-all-finite-individual-domains`, so it is consistent.
- `strong-possibility-r-implies-possibility-schema-r`: Maximalism (pure) is consistent (the
  maximalist root), so with `◇P` it is, for every consistent `P`; Strong Possibility gives
  `◇_≠◇P`, hence `◇P`.
-/

namespace Classicism

/-- `◇_≠◇p → ◇p`: `◇_≠` is below `◇`, and `4`. -/
theorem diaNe_dia_imp_dia (p : Prop) : P.DiaNe (◇ p) → ◇ p := fun h hn =>
  h ⟨True, trivial, modal_K _ _ (nec% (fun (hb : □ (¬ p)) (_ : ◇ True) (hd : ◇ p) =>
      not_dia_of_box_not p hb hd)) (modal_four _ ((box_not_eq p).mpr hn))⟩

#classicism_derive Classicism.diaNe_dia_imp_dia

namespace Meta

open AxiomSet

variable {Sig : Signature}

/-! ### No Pure Contingency -/

/-- `no-pure-contingency-and-atomlessness-imply-necessary-atomlessness`. -/
theorem npc_atomlessness_entails_necAtomlessness :
    npc Signature.pure ∪ P.Atomlessness.schema ⟹ P.NecAtomlessness.schema := by
  rintro a rfl
  exact npc_union_entails_box_pure P.Atomlessness.schema_closedTypes _ (AxiomSet.mem_box rfl)

/-- `no-pure-contingency-and-well-ordering-imply-necessary-well-ordering`, at every type. -/
theorem npc_wellOrdering_entails_necWellOrdering :
    npc Signature.pure ∪ P.WellOrdering.schema ⟹ P.NecWellOrdering.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  exact npc_union_entails_box_pure P.WellOrdering.schema_closedTypes _
    (AxiomSet.mem_box ⟨σ, hσ, rfl⟩)

/-! ### Maximalism against the necessitation of what a model refutes -/

/-- **Maximalism (pure) is inconsistent with the necessitation of a schema some model of `C`
refutes**: a failing instance has a consistent negation. -/
theorem maximalist_box_inconsistent_of_model {C : Type} [CategoryTheory.SmallCategory C]
    (M : Intensional.Premodel Signature.pure C) (hM : M.IsModel) {X N : AxiomSet Signature.pure}
    (hX : ClosedTypes X) (hf : ¬ M.HoldsAx X) (hN : X.box ⊆ N) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ N) := fun hc => hf fun p hp =>
  Classical.byContradiction fun hn =>
    max_box_inconsistent (Ax := empty) (Y := p)
      (Consistent.of_model M hM (Ax := empty ∪ single (Term.neg p)) fun a ha => ha.elim
        (fun h => h.elim) (fun h => by rw [show a = Term.neg p from h]; exact (M.holdsSentence_neg hM p).2 hn))
      (hX p hp)
      (Consistent.mono (fun a ha => ha.elim Or.inl (fun h => Or.inr (hN a (by
        rw [show a = Term.box p from h]; exact AxiomSet.mem_box hp)))) hc)

/-- Atomlessness fails in `Prop`: `⊤` is possible, and whatever is possible and below it is
true, hence `⊤`. -/
theorem not_atomlessness_holds_henkin : Sentence.holds henkin (Term.neg P.Atomlessness.quoted) := by
  simp only [Sentence.holds, Term.denote, Var.denote]
  intro h
  rcases h (True : Prop) with h1 | ⟨x₁, hx₁, _, hne⟩
  · exact h1 fun e => (show (∀ y : Prop, y) ∧ ¬ ∀ y : Prop, y from cast e trivial).2
      (show (∀ y : Prop, y) ∧ ¬ ∀ y : Prop, y from cast e trivial).1
  · refine hne (propext ⟨fun _ => trivial, fun _ => ?_⟩)
    by_contra hc
    exact hx₁ (propext ⟨fun h => absurd h hc, fun h => (h.2 h.1).elim⟩)

theorem not_atomlessness_consistent : Consistent (single (Term.neg P.Atomlessness.quoted)) :=
  Consistent.of_interp henkin fun _ h => h ▸ not_atomlessness_holds_henkin

/-- `maximalist-distinctness-incompatible-with-necessary-atomlessness`. -/
theorem maximalist_necAtomlessness_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecAtomlessness.schema) :=
  max_box_inconsistent (Consistent.empty_union not_atomlessness_consistent) rfl

/-- `possibility-and-necessary-relational-choice-incompatible`: Relational Choice fails in
`symmetric-all-surjections` (the argument `relational-choice` of `symmetric-ideally-full`). -/
theorem maximalist_necRelationalChoice_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecRelationalChoice.schema) :=
  have h := Map.Models.symmetric_all_surjections.relational_choice_r
  maximalist_box_inconsistent_of_model _ h.1 P.RelationalChoice.schema_closedTypes
    (by rw [← Intensional.Premodel.holdsAx_schemaIn_iff]; exact h.2)
    (by rintro _ ⟨_, ⟨_, _, hc₁, hc₂, rfl⟩, rfl⟩; exact ⟨_, _, hc₁, hc₂, rfl⟩)

/-! ### The Axiom of Infinity at `t` is consistent -/

/-- The Axiom of Infinity at `t` holds in `coalesced-all-finite-individual-domains`. -/
theorem axiomOfInfinityT_consistent : Consistent (single P.AxiomOfInfinityT.quoted) :=
  have h := Map.Models.coalesced_all_finite_individual_domains.axiom_of_infinity_t
  Consistent.of_model _ h.1 (by rw [← Intensional.Premodel.holdsAx_schemaIn_iff]; exact h.2)

/-- `possibility-schema-r-implies-possible-infinity-t`. -/
theorem possibility_entails_possibleInfinityT :
    possibility (empty : AxiomSet Signature.pure) ⟹ P.PossibleInfinityT.schema := by
  rintro a rfl
  exact Theorem.ax (possibility_mem rfl (Consistent.empty_union axiomOfInfinityT_consistent))

/-! ### Strong Possibility gives Possibility -/

/-- Maximalist Classicism (pure) is consistent: the maximalist root. -/
theorem maximalist_pure_consistent : Consistent (maximalist (Sig := Signature.pure)) :=
  Consistent.mono (fun _ ha => ha.elim (fun h => h.elim) id)
    Coalesced.maximalism_distinctness_consistent

/-- `strong-possibility-r-implies-possibility-schema-r`: for `P` consistent with `C`,
Maximalism proves `◇P`, so `◇P` is consistent with it, and Strong Possibility gives `◇_≠◇P`,
whence `◇P`. -/
theorem strongPossibility_entails_possibility :
    strongPossibility Signature.pure ⟹ possibility (empty : AxiomSet Signature.pure) := by
  rintro a ⟨hc, p, hp, rfl⟩
  have hcp : p.closedTypes = true := by simpa using hc
  have hcons : Consistent (maximalist ∪ single (Term.dia p)) :=
    Consistent.of_entails (Entails.union (Entails.refl _) (fun b hb => by
      rw [show b = Term.dia p from hb]
      exact maximalist_entails_possibility _ (possibility_mem hcp hp))) maximalist_pure_consistent
  have hmem : strongPossibility Signature.pure (Term.diaNe (Term.dia p)) :=
    ⟨by simpa [Term.diaNe, Term.closedTypes_rename] using hcp, Term.dia p, hcons, rfl⟩
  exact Theorem.mp (Derivable.allEβ (Theorem.ofCMinus diaNe_dia_imp_dia.derivable) p)
    (Theorem.ax hmem)

end Meta

end Classicism
