import Classicism.Results.SentenceSchemas.WitnessedPossibility
import Classicism.Results.SentenceSchemas.PossibilityDistinctness
import Classicism.Completeness.ConstantBlocks
import Classicism.Syntax.Inhabited

/-!
# Separated Structure, Independence and the signature schemas

The map's results about the Σ-combinatorialism family that put terms for constants or
variables for constants in derivations (`Completeness/ConstantBlocks.lean`):

- **Iterated Separated Structure** (`ss_iter`): `F d̄ = G d̄ → F = G` for distinct constants
  `d̄` occurring in neither `F` nor `G`, peeling one constant at a time; and its form for a
  formula (`ss_box`): `□P[d̄/x̄] → λx̄. P = λx̄. ⊤`.
- `separated-structure-r-implies-possibly-witnessed-possibility-r`,
  `separated-structure-r-implies-independence-signature-r`,
  `pure-distinctness-and-separated-structure-imply-signature-distinctness`: from `ss_box`.
- `distinctness-signature-r-implies-separated-structure-r`: where `Fc = Gc` is a theorem,
  the variable put for `c` (`CMap.abstract`) makes `∀x. Fx = Gx` one, and Modalized
  Functionality gives `F = G`; otherwise Distinctness refutes `Fc = Gc`.
- `possibility-signature-r-implies-witnessed-possibility-r`: where `P[c̄/x̄]` is consistent,
  Possibility; otherwise `C ⊢ ¬P[c̄/x̄]`, so `C ⊢ ¬P` with the block put back for the
  constants (`Term.cmap_block_subst_consts`), and `∃x̄. P` is refutable.
- `possibly-witnessed-possibility-r-implies-separated-structure-r`: the constants of `F`,
  `G` other than `c` abstracted (`Term.exists_abstract`), Possibly Witnessed Possibility at
  `¬(F°ȳx = G°ȳx)`, then Modalized Functionality; and
  `logical-necessity-r-implies-separated-structure-r` through Possibly Witnessed Possibility.
- `witnessed-possibility-r-implies-independence-signature-r`: Witnessed Possibility at
  `x ≠ Aȳ`, whose closure is a theorem.
- `logical-necessity-r-implies-modal-freedom-signature-r`.
-/

namespace Classicism

section shallow

/-- Separated Structure gives Possibly Witnessed Possibility: `□¬a` gives `e`, a necessary
truth when true, which necessitates `¬g`. -/
theorem ss_pwp_glue (a g e : Prop) : (□ ¬ a → e) → (e → □ e) → □ (e → ¬ g) → ◇ g → ◇ a :=
  fun h1 h2 h3 hg => (em (◇ a)).elim id fun hna =>
    absurd hg (not_dia_of_box_not g (modal_K _ _ h3 (h2 (h1 (box_not_of_not_dia a hna)))))

/-- Logical Necessity gives Possibly Witnessed Possibility: at `¬a`, and with no constants
at `f`. -/
theorem ln_pwp_glue (a f g : Prop) : (□ ¬ a ↔ f) → (□ f ↔ f) → □ (f → ¬ g) → ◇ g → ◇ a :=
  fun h1 h2 h3 hg => (em (◇ a)).elim id fun hna =>
    absurd hg (not_dia_of_box_not g (modal_K _ _ h3 (h2.2 (h1.1 (box_not_of_not_dia a hna)))))

end shallow

#classicism_derive Classicism.ss_pwp_glue Classicism.ln_pwp_glue Classicism.modalized_functionality

namespace Meta

open AxiomSet

variable {Sig : Signature}

/-! ### Block forms: constants, types, conversions -/

namespace Term

theorem consts_lamBlock : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy} (b : Term Sig (Ctx.block σs Γ) ρ),
    (lamBlock σs b).consts = b.consts
  | [], _, _, _ => rfl
  | _ :: σs, _, _, b => consts_lamBlock σs (Γ := _ :: _) b

theorem closedTypes_lamBlock : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy} (b : Term Sig (Ctx.block σs Γ) ρ),
    (lamBlock σs b).closedTypes = (σs.all (fun σ => decide σ.Closed) && b.closedTypes)
  | [], _, _, _ => by simp [lamBlock]
  | σ :: σs, _, _, b => by
    simp only [lamBlock, closedTypes, closedTypes_lamBlock σs b, List.all_cons, Bool.and_assoc]

theorem ofPure_lamBlock : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy} (b : Term Signature.pure (Ctx.block σs Γ) ρ),
    Term.ofPure (Sig := Sig) (lamBlock σs b) = lamBlock σs (Term.ofPure b)
  | [], _, _, _ => rfl
  | _ :: σs, _, _, b => by
    show Term.ofPure (Term.lam (lamBlock σs b)) = Term.lam (lamBlock σs (Term.ofPure b))
    rw [ofPure_lam, ofPure_lamBlock σs b]

theorem consts_ofPure : ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ),
    (Term.ofPure (Sig := Sig) t).consts = ∅ :=
  fun t => consts_eq_empty_of_pure _ (pure_ofPure t)

end Term

/-- `□`'s right side is `⊤` in every context: substitution leaves it. -/
theorem Term.subst_top {Γ Δ : Ctx} (s : Sub Sig Γ Δ) : (Term.top : Formula Sig Γ).subst s = Term.top := rfl

/-- Conversion of the two sides of an implication. -/
theorem Conv.imp_congr {Γ : Ctx} {p p' q q' : Formula Sig Γ} (hp : p ≡ p') (hq : q ≡ q') :
    Term.imp p q ≡ Term.imp p' q' :=
  Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.app_congr (Conv.refl _) hp)) hq

/-- Conversion of the two sides of an identity. -/
theorem Conv.eq_congr {Γ : Ctx} {σ : Ty} {a a' b b' : Term Sig Γ σ} (ha : a ≡ a') (hb : b ≡ b') :
    Term.eq' a b ≡ Term.eq' a' b' :=
  Conv.app_congr (Conv.app_congr (Conv.refl _) ha) hb

/-- The theorems of `C` with the empty schema are those of `C`. -/
theorem theorem_union_empty {p : Sentence Sig} :
    Theorem (C.axioms ∪ (empty : AxiomSet Sig)) p ↔ C.Theorem p :=
  ⟨fun h => Derivable.mono (fun _ h => h.elim id False.elim) h, fun h => Theorem.ofC h⟩

namespace Derivable

variable {Ax : AxiomSet Sig}

/-- `λx̄. P = λx̄. ⊤` gives `∀x̄. P`: Leibniz's Law at the block quantifier. -/
theorem forallBlock_of_lamBlock_eq_top (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    {P : Formula Sig (Ctx.block σs Γ)}
    (h : Derivable Ax Δ (Term.eq' (Term.lamBlock σs P) (Term.lamBlock σs Term.top))) :
    Derivable Ax Δ (Term.forallBlock σs P) :=
  conv (ll (Term.allC σs) (eqSymm h) (allIC σs top)) (Conv.allC_lamBlock σs P)

/-- `¬∃x̄. ¬P` gives `∀x̄. P`. -/
theorem forallBlock_of_not_existsBlock_neg (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    {P : Formula Sig (Ctx.block σs Γ)}
    (h : Derivable Ax Δ (Term.neg (Term.existsBlock σs (Term.neg P)))) :
    Derivable Ax Δ (Term.forallBlock σs P) :=
  allIBlock σs (orE (em P) hyp₀
    (notE (exIBlock_vars σs hyp₀) (weaken₁ (rename (Ren.wkBlock σs) h))))

end Derivable

/-! ### Iterated Separated Structure -/

/-- **Iterated Separated Structure**: `F d̄ = G d̄ → F = G`, for distinct constants `d̄` in
neither `F` nor `G`, by Separated Structure at each constant, the last first. -/
theorem ss_iter {X : AxiomSet Sig} (hX : separatedStructure Sig ⊆ X) :
    ∀ (ds : List Sig.Const) {ρ : RTy} (F G : Term Sig [] (ds.map Sig.typeOf ⇒* ρ)), ds.Nodup →
    (∀ d ∈ ds, d ∉ F.consts ∧ d ∉ G.consts) → F.closedTypes = true → G.closedTypes = true →
    Theorem (C.axioms ∪ X) (Term.imp (Term.eq' (Term.appBlock F (Terms.consts ds))
      (Term.appBlock G (Terms.consts ds))) (Term.eq' F G))
  | [], _, _, _, _, _, _, _ => Derivable.impI Derivable.hyp₀
  | d :: ds, ρ, F, G, hnd, hc, hF, hG => by
    have hd : d ∉ ds := (List.nodup_cons.1 hnd).1
    have hcl := Term.closed_of_closedTypes hF
    have hτ : (Sig.typeOf d).Closed := hcl.1
    have hτ' : (ds.map Sig.typeOf ⇒* ρ).Closed := hcl.2
    have fresh : ∀ (H : Term Sig [] ((d :: ds).map Sig.typeOf ⇒* ρ)), (∀ d' ∈ d :: ds, d' ∉ H.consts) →
        ∀ d' ∈ ds, d' ∉ (Term.app H (Term.const d)).consts := by
      intro H hH d' hd' h'
      rcases h' with h' | h'
      · exact hH d' (List.mem_cons_of_mem _ hd') h'
      · exact hd (by rw [Set.mem_singleton_iff.1 h'] at hd'; exact hd')
    have ih := ss_iter hX ds (Term.app F (Term.const d)) (Term.app G (Term.const d))
      (List.nodup_cons.1 hnd).2
      (fun d' hd' => ⟨fresh F (fun d' h => (hc d' h).1) d' hd', fresh G (fun d' h => (hc d' h).2) d' hd'⟩)
      (by simp [Term.closedTypes, hF, hτ]) (by simp [Term.closedTypes, hG, hτ])

    have hs : Theorem (C.axioms ∪ X) (Term.imp (Term.eq' (Term.app F (Term.const d))
        (Term.app G (Term.const d))) (Term.eq' F G)) :=
      Theorem.ax (hX _ ⟨by simp [Term.closedTypes, hF, hG, hτ, hτ'], d, _, F, G,
        (hc d List.mem_cons_self).1, (hc d List.mem_cons_self).2, rfl⟩)
    exact Derivable.impI (Derivable.impE (Derivable.weaken₁ hs)
      (Derivable.impE (Derivable.weaken₁ ih) Derivable.hyp₀))

/-- **Iterated Separated Structure for a formula**: `□P[d̄/x̄] → λx̄. P = λx̄. ⊤`, for a
formula `P` in the block of the distinct constants `d̄`, none of which occurs in it. -/
theorem ss_box {X : AxiomSet Sig} (hX : separatedStructure Sig ⊆ X) (cs : List Sig.Const)
    (hnd : cs.Nodup) (P : Formula Sig (Ctx.block (cs.map Sig.typeOf) []))
    (hP : ∀ c ∈ cs, c ∉ P.consts) (hcl : (Term.lamBlock _ P).closedTypes = true) :
    Theorem (C.axioms ∪ X) (Term.imp (Term.box (P.subst (Sub.consBlock (Terms.constsAt [] cs) Sub.id)))
      (Term.eq' (Term.lamBlock _ P) (Term.lamBlock _ Term.top))) := by
  have hcl' : (Term.lamBlock (Γ := []) (cs.map Sig.typeOf) (Term.top : Formula Sig _)).closedTypes = true := by
    rw [Term.closedTypes_lamBlock] at hcl ⊢
    simp only [Bool.and_eq_true] at hcl
    simp [hcl.1]
  have h := ss_iter hX cs (Term.lamBlock _ P) (Term.lamBlock _ Term.top) hnd
    (fun c hc => ⟨by rw [Term.consts_lamBlock]; exact hP c hc,
      by rw [Term.consts_lamBlock]; exact fun h => by simp [Term.consts] at h⟩) hcl hcl'
  rw [Terms.consts_eq_constsAt] at h
  refine Derivable.conv h (Conv.imp_congr (Conv.eq_congr (Conv.appBlock_lamBlock _ P _) ?_) (Conv.refl _))
  exact Conv.appBlock_lamBlock _ Term.top _

/-! ### Separated Structure gives Possibly Witnessed Possibility -/

/-- The block quantifiers, read in a signature, keep the paper's language when the block's
types are closed. -/
local macro "split_closed " h:ident : tactic => `(tactic| simp only [Term.closedTypes_imp,
  Term.closedTypes_iff, Term.closedTypes_dia, Term.closedTypes_box, Term.closedTypes_conj,
  Term.closedTypes_neg, Term.closedTypes_ofPure, Term.closedTypes_atConsts,
  Term.closedTypes_forallBlock_eq_existsBlock, Term.closedTypes_eq', Term.closedTypes_bot,
  Term.closedTypes_top, Term.closedTypes_forall', Term.closedTypes_var, Ty.closed_rel,
  RTy.closed_t, decide_true, Bool.and_true, Bool.and_eq_true, and_true] at $h:ident)

/-- `atConsts`, as the block substitution of `Terms.constsAt`. -/
theorem atConsts_eq (cs : List Sig.Const)
    (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])) :
    Term.atConsts cs P = (Term.ofPure P).subst (Sub.consBlock (Terms.constsAt [] cs) Sub.id) := by
  rw [Term.atConsts, Terms.consts_eq_constsAt]

/-- `separated-structure-r-implies-possibly-witnessed-possibility-r`. -/
theorem separatedStructure_entails_possiblyWitnessedPossibility :
    separatedStructure Sig ⟹ possiblyWitnessedPossibility Sig := by
  rintro a ⟨hc, cs, P, hcs, rfl⟩
  split_closed hc
  have hex := hc.1
  rw [Term.closedTypes_existsBlock] at hex
  simp only [Bool.and_eq_true] at hex
  let L : Term Sig [] _ := Term.lamBlock (cs.map Sig.typeOf) (Term.neg (Term.ofPure P))
  let e : Sentence Sig := Term.eq' L (Term.lamBlock (cs.map Sig.typeOf) Term.top)
  have h1 : Theorem (C.axioms ∪ separatedStructure Sig)
      (Term.imp (Term.box (Term.neg (Term.atConsts cs P))) e) := by
    rw [atConsts_eq]
    exact ss_box (fun _ h => h) cs hcs (Term.neg (Term.ofPure P))
      (fun c _ h => by
        have : (Term.neg (Term.ofPure (Sig := Sig) P)).consts = ∅ := Term.consts_ofPure (Term.neg P)
        rw [this] at h; exact h)
      (by rw [Term.closedTypes_lamBlock]; simp [hex.1, hex.2])
  have h2 : C.Theorem (Term.imp e (Term.box e)) := Completeness.nec_identity _ _
  have h3 : C.Theorem (Term.box (Term.imp e (Term.neg (Term.ofPure (Term.existsBlock _ P))))) := by
    refine C.Theorem.nec (Derivable.impI ?_)
    rw [Term.ofPure_existsBlock]
    exact Derivable.notI (q := Term.top)
      (Derivable.existsBlock_forallBlock_neg _ Derivable.hyp₀
        (Derivable.forallBlock_of_lamBlock_eq_top _ (Derivable.weaken₁ Derivable.hyp₀)))
      (Derivable.existsBlock_forallBlock_neg _ Derivable.hyp₀
        (Derivable.forallBlock_of_lamBlock_eq_top _ (Derivable.weaken₁ Derivable.hyp₀)))
  exact Theorem.mp (Theorem.mp₂ (Derivable.allE₃β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure ss_pwp_glue.derivable)) _ _ e) h1 (Theorem.ofC h2))
    (Theorem.ofC h3)

/-! ### Logical Necessity gives Possibly Witnessed Possibility -/

/-- Logical Necessity gives Possibly Witnessed Possibility: at `¬P`, and with no constants
at `∀x̄. ¬P`. -/
theorem logicalNecessity_entails_possiblyWitnessedPossibility :
    logicalNecessity Sig ⟹ possiblyWitnessedPossibility Sig := by
  rintro a ⟨hc, cs, P, hcs, rfl⟩
  split_closed hc
  have h1 : Theorem (C.axioms ∪ logicalNecessity Sig)
      (Term.iff (Term.box (Term.atConsts cs (Term.neg P))) (Term.ofPure (Term.forallBlock _ (Term.neg P)))) :=
    Theorem.ax (logicalNecessity_mem hcs (by rw [closedTypes_existsBlock_neg]; exact hc.1))
  have h2 : Theorem (C.axioms ∪ logicalNecessity Sig)
      (Term.iff (Term.box (Term.atConsts [] (Term.forallBlock _ (Term.neg P))))
        (Term.ofPure (Term.forallBlock [] (Term.forallBlock _ (Term.neg P))))) :=
    Theorem.ax (logicalNecessity_mem List.nodup_nil (by
      show (Term.forallBlock _ (Term.neg P)).closedTypes = true
      rw [Term.closedTypes_forallBlock_eq_existsBlock, closedTypes_existsBlock_neg]; exact hc.1))
  rw [Term.atConsts_nil] at h2
  have h3 : C.Theorem (Sig := Sig) (Term.box (Term.imp (Term.ofPure (Term.forallBlock _ (Term.neg P)))
      (Term.neg (Term.ofPure (Term.existsBlock _ P))))) := by
    refine C.Theorem.nec (Derivable.impI ?_)
    rw [Term.ofPure_existsBlock, Term.ofPure_forallBlock]
    exact Derivable.notI (q := Term.top)
      (Derivable.existsBlock_forallBlock_neg _ Derivable.hyp₀ (Derivable.weaken₁ Derivable.hyp₀))
      (Derivable.existsBlock_forallBlock_neg _ Derivable.hyp₀ (Derivable.weaken₁ Derivable.hyp₀))
  exact Theorem.mp (Theorem.mp₂ (Derivable.allE₃β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure ln_pwp_glue.derivable)) _ _ _) h1 h2) (Theorem.ofC h3)

end Meta

end Classicism
