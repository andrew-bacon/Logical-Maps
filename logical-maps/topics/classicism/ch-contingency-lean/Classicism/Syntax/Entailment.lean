import Classicism.Syntax.Axioms

/-!
# Entailment between axiom sets

The map's arrows are facts of the form "this schema entails that schema": a relation
between *axiom sets*, each element of the second derivable from the first together with
Classicism. This module defines it and proves its algebra: reflexivity, transitivity (a
cut lemma, replacing axioms by their derivations), monotonicity, unions, and how a family
of implications `∀ σ. P σ → Q σ` proved in `C` gives `{P σ} ⟹ {Q σ}`; the deduction
theorem for axiom sets (an axiom becomes a hypothesis); and consistency of an axiom set
with `C`, with the two ways it turns into non-theoremhood and back. The sentence schemas
that use these — Distinctness, Possibility, maximalization — are in
`SentenceSchemas.lean`.

Semantics — that entailment transfers holding, in `Prop` and in an action model — is in
`Denotation.lean` and `ActionSoundness.lean`, with the soundness theorems it rests on.
-/

namespace Classicism.Meta

universe u v w

variable {Sig : Signature}

/-! ### Axiom sets -/

namespace AxiomSet

/-- The empty set. -/
def empty : AxiomSet Sig := fun _ => False

/-- One sentence. -/
def single (a : Sentence Sig) : AxiomSet Sig := fun b => b = a

/-- Union. -/
protected def union (Ax₁ Ax₂ : AxiomSet Sig) : AxiomSet Sig := fun a => Ax₁ a ∨ Ax₂ a

instance : Union (AxiomSet Sig) := ⟨AxiomSet.union⟩

/-- Inclusion. -/
protected def Subset (Ax₁ Ax₂ : AxiomSet Sig) : Prop := ∀ a, Ax₁ a → Ax₂ a

instance : HasSubset (AxiomSet Sig) := ⟨AxiomSet.Subset⟩

/-- The instances of a schema: the sentences `P i` for `i` ranging over the schema's
parameters (its object types, typically). -/
def ofFamily {ι : Sort u} (P : ι → Sentence Sig) : AxiomSet Sig := fun a => ∃ i, a = P i

theorem mem_union_left {Ax₁ Ax₂ : AxiomSet Sig} {a : Sentence Sig} (h : Ax₁ a) : (Ax₁ ∪ Ax₂) a :=
  Or.inl h
theorem mem_union_right {Ax₁ Ax₂ : AxiomSet Sig} {a : Sentence Sig} (h : Ax₂ a) : (Ax₁ ∪ Ax₂) a :=
  Or.inr h
theorem subset_union_left (Ax₁ Ax₂ : AxiomSet Sig) : Ax₁ ⊆ Ax₁ ∪ Ax₂ := fun _ => Or.inl
theorem subset_union_right (Ax₁ Ax₂ : AxiomSet Sig) : Ax₂ ⊆ Ax₁ ∪ Ax₂ := fun _ => Or.inr
theorem mem_ofFamily {ι : Sort u} (P : ι → Sentence Sig) (i : ι) : ofFamily P (P i) := ⟨i, rfl⟩

end AxiomSet

/-- The logical part of `C` with any axioms is `C`. -/
theorem C.logical_union (Ax : AxiomSet Sig) : ∀ a, (C.axioms ∪ Ax).logical a ↔ C.axioms a :=
  fun _ => ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩

/-! ### Replacing axioms by their derivations -/

namespace Derivable

/-- A derivation from axioms each of which is a theorem of another set is a derivation
from that set: `mono`, with derivations in place of axioms, provided the logical part
of the one set is included in the other's, for Subst's premises. The closed derivation
of an axiom is renamed into the context and weakened. -/
theorem replaceAx : ∀ {Ax Ax' : AxiomSet Sig}, (∀ a, Ax a → Theorem Ax' a) →
    (∀ a, Ax.logical a → Ax'.logical a) →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derivable Ax Δ p → Derivable Ax' Δ p
  | _, _, _, _, _, _, _, hyp h => hyp h
  | _, _, hA, _, Γ, _, _, ax (a := a) h =>
    weaken (rename (Ren.ofEmpty (Γ := Γ)) (hA a h)) (List.nil_subset _)
  | _, _, hA, hL, _, _, _, andI h₁ h₂ => andI (replaceAx hA hL h₁) (replaceAx hA hL h₂)
  | _, _, hA, hL, _, _, _, andE₁ h => andE₁ (replaceAx hA hL h)
  | _, _, hA, hL, _, _, _, andE₂ h => andE₂ (replaceAx hA hL h)
  | _, _, hA, hL, _, _, _, orI₁ h => orI₁ (replaceAx hA hL h)
  | _, _, hA, hL, _, _, _, orI₂ h => orI₂ (replaceAx hA hL h)
  | _, _, hA, hL, _, _, _, orE h h₁ h₂ => orE (replaceAx hA hL h) (replaceAx hA hL h₁) (replaceAx hA hL h₂)
  | _, _, hA, hL, _, _, _, notI h₁ h₂ => notI (replaceAx hA hL h₁) (replaceAx hA hL h₂)
  | _, _, hA, hL, _, _, _, notE h₁ h₂ => notE (replaceAx hA hL h₁) (replaceAx hA hL h₂)
  | _, _, hA, hL, _, _, _, em p => em p
  | _, _, hA, hL, _, _, _, allE h a => allE (replaceAx hA hL h) a
  | _, _, hA, hL, _, _, _, allI h => allI (replaceAx hA hL h)
  | _, _, hA, hL, _, _, _, exI a h => exI a (replaceAx hA hL h)
  | _, _, hA, hL, _, _, _, exE h h' => exE (replaceAx hA hL h) (replaceAx hA hL h')
  | _, _, hA, hL, _, _, _, refl a => refl a
  | _, _, hA, hL, _, _, _, ll F h₁ h₂ => ll F (replaceAx hA hL h₁) (replaceAx hA hL h₂)
  | _, _, hA, hL, _, _, _, subst C h₁ h₂ h₃ =>
    subst C (mono hL h₁) (mono hL h₂) (replaceAx hA hL h₃)
  | _, _, hA, hL, _, _, _, conv h c => conv (replaceAx hA hL h) c
/-- Cut for axiom sets over Classicism: if every sentence of `Ax'` is a theorem of
`C ∪ Ax₁`, a derivation from `C ∪ Ax'` is one from `C ∪ Ax₁`. The logical part of both
sets is `C` itself, which is what lets Subst's premises carry over. -/
theorem cut {Ax₁ Ax' : AxiomSet Sig} (hA : ∀ a, Ax' a → Theorem (C.axioms ∪ Ax₁) a)
    {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} (h : Derivable (C.axioms ∪ Ax') Δ p) :
    Derivable (C.axioms ∪ Ax₁) Δ p :=
  replaceAx (fun a ha => ha.elim (fun h => Derivable.axiom (Or.inl h)) (hA a))
    (fun a ha => (C.logical_union Ax₁ a).2 ((C.logical_union Ax' a).1 ha)) h

end Derivable

/-! ### An axiom as a hypothesis: the deduction theorem -/

theorem _root_.Classicism.Meta.Term.close_weaken {Γ : Ctx} {τ σ : Ty} (a : Term Sig [] σ) :
    (a.close : Term Sig Γ σ).weaken (τ := τ) = a.close := by
  simp only [Term.close, Term.weaken, Term.rename_rename]
  congr 1; funext σ v; exact nomatch v

theorem _root_.List.cons_cons_subset_swap {α : Type} (x y : α) (l : List α) :
    x :: y :: l ⊆ y :: x :: l := by
  intro z hz
  simp only [List.mem_cons] at hz ⊢
  rcases hz with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

namespace Derivable

/-- **An axiom becomes a hypothesis.** A derivation from a set whose axioms are all in
`Ax` or are the sentence `a` is a derivation from `Ax` with `a` among the hypotheses.
By induction; the eigenvariable rules need that the closed `a` is unchanged by
weakening, and Subst's premises, which are derived in the logical part of the set, need
that `a` is already in `Ax` when it is logical (`hL`), since a hypothesis cannot enter
them. -/
theorem ofAxiom : ∀ {Ax' Ax : AxiomSet Sig} {a : Sentence Sig}, (∀ b, Ax' b → Ax b ∨ b = a) →
    (Logical a → Ax a) →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derivable Ax' Δ p → Derivable Ax (a.close :: Δ) p
  | _, _, _, _, _, _, _, _, hyp h => hyp (List.mem_cons_of_mem _ h)
  | _, _, _, hA, _, _, _, _, ax (a := b) h => (hA b h).elim (fun hb => weaken₁ (ax hb)) (fun hb => by
      subst hb; exact hyp₀)
  | _, _, _, hA, hL, _, _, _, andI h₁ h₂ => andI (ofAxiom hA hL h₁) (ofAxiom hA hL h₂)
  | _, _, _, hA, hL, _, _, _, andE₁ h => andE₁ (ofAxiom hA hL h)
  | _, _, _, hA, hL, _, _, _, andE₂ h => andE₂ (ofAxiom hA hL h)
  | _, _, _, hA, hL, _, _, _, orI₁ h => orI₁ (ofAxiom hA hL h)
  | _, _, _, hA, hL, _, _, _, orI₂ h => orI₂ (ofAxiom hA hL h)
  | _, _, _, hA, hL, _, _, _, orE h h₁ h₂ =>
    orE (ofAxiom hA hL h) (weaken (ofAxiom hA hL h₁) (List.cons_cons_subset_swap _ _ _))
      (weaken (ofAxiom hA hL h₂) (List.cons_cons_subset_swap _ _ _))
  | _, _, _, hA, hL, _, _, _, notI h₁ h₂ =>
    notI (weaken (ofAxiom hA hL h₁) (List.cons_cons_subset_swap _ _ _))
      (weaken (ofAxiom hA hL h₂) (List.cons_cons_subset_swap _ _ _))
  | _, _, _, hA, hL, _, _, _, notE h₁ h₂ => notE (ofAxiom hA hL h₁) (ofAxiom hA hL h₂)
  | _, _, _, _, _, _, _, _, em p => em p
  | _, _, _, hA, hL, _, _, _, allE h a => allE (ofAxiom hA hL h) a
  | _, _, _, hA, hL, _, _, _, exI a h => exI a (ofAxiom hA hL h)
  | _, _, a, hA, hL, _, Δ, _, allI (σ := σ) h => allI (by
      show Derivable _ ((a.close : Formula Sig _).weaken (τ := σ) :: Hyps.weaken Δ) _
      rw [Term.close_weaken]
      exact ofAxiom hA hL h)
  | _, _, a, hA, hL, _, Δ, _, exE (σ := σ) h h' => exE (ofAxiom hA hL h) (by
      show Derivable _ (_ :: (a.close : Formula Sig _).weaken (τ := σ) :: Hyps.weaken Δ) _
      rw [Term.close_weaken]
      exact weaken (ofAxiom hA hL h') (List.cons_cons_subset_swap _ _ _))
  | _, _, _, _, _, _, _, _, refl a => refl a
  | _, _, _, hA, hL, _, _, _, ll F h₁ h₂ => ll F (ofAxiom hA hL h₁) (ofAxiom hA hL h₂)
  | _, _, _, hA, hL, _, _, _, subst C h₁ h₂ h₃ =>
    have hl : ∀ b, (_ : AxiomSet Sig).logical b → (_ : AxiomSet Sig).logical b :=
      fun b ⟨hb, hlb⟩ => ⟨(hA b hb).elim id (fun e => by subst e; exact hL hlb), hlb⟩
    subst C (mono hl h₁) (mono hl h₂) (ofAxiom hA hL h₃)
  | _, _, _, hA, hL, _, _, _, conv h c => conv (ofAxiom hA hL h) c

end Derivable

/-- **The deduction theorem** for axiom sets: a theorem of `Ax` with the sentence `a` is,
under `Ax`, implied by `a`. The side condition says that `a`, if logical, is already in
`Ax`; for `C` with any axioms it is automatic (`deductionC`). -/
theorem Theorem.deduction {Ax : AxiomSet Sig} {a q : Sentence Sig} (hL : Logical a → Ax a)
    (h : Theorem (Ax ∪ AxiomSet.single a) q) : Theorem Ax (Term.imp a q) := by
  have := Derivable.ofAxiom (fun _ hb => hb) hL h
  rw [Term.close_nil] at this
  exact Derivable.impI this

/-- The deduction theorem over Classicism: `existence_e` is already in `C`. Stated for
`C ∪ (Ax ∪ {a})`, the form in which `Consistent (Ax ∪ single a)` unfolds. -/
theorem Theorem.deductionC {Ax : AxiomSet Sig} {a q : Sentence Sig}
    (h : Theorem (C.axioms ∪ (Ax ∪ AxiomSet.single a)) q) :
    Theorem (C.axioms ∪ Ax) (Term.imp a q) :=
  Theorem.deduction (fun hl => Or.inl hl)
    (Derivable.mono (fun _ hb => hb.elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)) h)

/-! ### Theorems of `C` with an axiom set, as rules

The three moves a metalogical proof makes when it descends into the object language:
cite an axiom of the set, cite a theorem of Classicism, and apply an implication. -/

namespace Theorem

variable {Ax : AxiomSet Sig}

/-- An axiom of the set is a theorem of `C` with the set. -/
theorem ax {a : Sentence Sig} (h : Ax a) : Theorem (C.axioms ∪ Ax) a :=
  Derivable.axiom (Or.inr h)

/-- A theorem of Classicism is a theorem of Classicism with any axiom set. -/
theorem ofC {a : Sentence Sig} (h : C.Theorem a) : Theorem (C.axioms ∪ Ax) a :=
  Derivable.mono (fun _ => Or.inl) h

/-- A theorem of `C⁻` likewise: the form in which the translator derives most lemmas. -/
theorem ofCMinus {a : Sentence Sig} (h : C.TheoremMinus a) : Theorem (C.axioms ∪ Ax) a :=
  Derivable.mono (fun _ h => h.elim) h

/-- Modus ponens. -/
theorem mp {p q : Sentence Sig} (h : Theorem Ax (Term.imp p q)) (hp : Theorem Ax p) :
    Theorem Ax q :=
  Derivable.impE h hp

/-- Modus ponens with two premises. -/
theorem mp₂ {p q r : Sentence Sig} (h : Theorem Ax (Term.imp p (Term.imp q r)))
    (hp : Theorem Ax p) (hq : Theorem Ax q) : Theorem Ax r :=
  Derivable.impE (Derivable.impE h hp) hq

/-- **Necessitation**: what `C` proves, it proves necessary. `p` and `⊤` are each derivable
from the other in the logical part, so Subst turns `⊤ = ⊤` into `p = ⊤`, which is `□p`.
(Only for theorems of `C`: the premises of Subst carry no axioms.) -/
theorem _root_.Classicism.Meta.C.Theorem.nec {p : Sentence Sig} (h : C.Theorem p) :
    C.Theorem (Term.box p) :=
  Derivable.subst (P := Term.top) (Q := p) (Hole.appL (Hole.appR (Term.eq _) Hole.hole) Term.top)
    (Derivable.weaken₁ (Derivable.mono (fun _ ha => ⟨ha, ha⟩) h))
    Derivable.top
    (Derivable.refl Term.top)

/-- A theorem under an equal sentence: where a sentence and the form it is meant as are
equal but not by computation, as a vectorized sentence and a list form are equal up to
the translations of closed types (`classicism_vec_eq`). -/
theorem cast {p q : Sentence Sig} (h : Theorem Ax p) (e : p = q) : Theorem Ax q := e ▸ h

end Theorem

/-! ### Entailment -/

namespace AxiomSet

/-- **Entailment relative to Classicism**: every sentence of `Ax₂` is a theorem of `C`
together with `Ax₁`. The map's arrows. -/
def Entails (Ax₁ Ax₂ : AxiomSet Sig) : Prop := ∀ a, Ax₂ a → Theorem (C.axioms ∪ Ax₁) a

@[inherit_doc] infix:50 " ⟹ " => Entails

namespace Entails

variable {Ax₁ Ax₂ Ax₃ : AxiomSet Sig}

theorem of_subset (h : Ax₂ ⊆ Ax₁) : Ax₁ ⟹ Ax₂ :=
  fun a ha => Derivable.axiom (Or.inr (h a ha))

theorem refl (Ax : AxiomSet Sig) : Ax ⟹ Ax := of_subset fun _ h => h

theorem trans (h₁ : Ax₁ ⟹ Ax₂) (h₂ : Ax₂ ⟹ Ax₃) : Ax₁ ⟹ Ax₃ :=
  fun a ha => Derivable.cut h₁ (h₂ a ha)

theorem mono_left (h : Ax₁ ⊆ Ax₂) (e : Ax₁ ⟹ Ax₃) : Ax₂ ⟹ Ax₃ :=
  fun a ha => Derivable.mono (fun b hb => hb.elim Or.inl (fun hb => Or.inr (h b hb))) (e a ha)

theorem mono_right (h : Ax₃ ⊆ Ax₂) (e : Ax₁ ⟹ Ax₂) : Ax₁ ⟹ Ax₃ :=
  fun a ha => e a (h a ha)

theorem union (h₁ : Ax₁ ⟹ Ax₂) (h₂ : Ax₁ ⟹ Ax₃) : Ax₁ ⟹ Ax₂ ∪ Ax₃ :=
  fun a ha => ha.elim (h₁ a) (h₂ a)

theorem union_left (Ax₁ Ax₂ : AxiomSet Sig) : Ax₁ ∪ Ax₂ ⟹ Ax₁ := of_subset (subset_union_left _ _)
theorem union_right (Ax₁ Ax₂ : AxiomSet Sig) : Ax₁ ∪ Ax₂ ⟹ Ax₂ := of_subset (subset_union_right _ _)

/-- Classicism alone entails what it proves. -/
theorem of_theorem {a : Sentence Sig} (h : C.Theorem a) : (empty : AxiomSet Sig) ⟹ single a :=
  fun _ hb => hb ▸ Derivable.mono (fun _ => Or.inl) h

/-- A family of implications `P (f k) → Q k` proved in `C` entails the schema `Q` from the
schema `P`: the form of the map's arrows between type-indexed principles. -/
theorem of_imp_family {ι : Sort u} {κ : Sort v} (P : ι → Sentence Sig) (Q : κ → Sentence Sig) (f : κ → ι)
    (h : ∀ k, C.Theorem (Term.imp (P (f k)) (Q k))) : ofFamily P ⟹ ofFamily Q := by
  rintro a ⟨k, rfl⟩
  exact Derivable.impE (Derivable.mono (fun _ => Or.inl) (h k)) (Derivable.axiom (Or.inr ⟨f k, rfl⟩))

/-- Two premises. -/
theorem of_imp_family₂ {ι₁ : Sort u} {ι₂ : Sort v} {κ : Sort w} (P₁ : ι₁ → Sentence Sig) (P₂ : ι₂ → Sentence Sig)
    (Q : κ → Sentence Sig) (f₁ : κ → ι₁) (f₂ : κ → ι₂)
    (h : ∀ k, C.Theorem (Term.imp (P₁ (f₁ k)) (Term.imp (P₂ (f₂ k)) (Q k)))) :
    ofFamily P₁ ∪ ofFamily P₂ ⟹ ofFamily Q := by
  rintro a ⟨k, rfl⟩
  exact Derivable.impE
    (Derivable.impE (Derivable.mono (fun _ => Or.inl) (h k))
      (Derivable.axiom (Or.inr (Or.inl ⟨f₁ k, rfl⟩))))
    (Derivable.axiom (Or.inr (Or.inr ⟨f₂ k, rfl⟩)))

end Entails

/-! ### Consistency -/

/-- `Ax` is consistent (with Classicism): `⊥` is not a theorem of `C ∪ Ax`. -/
def Consistent (Ax : AxiomSet Sig) : Prop := ¬ Theorem (C.axioms ∪ Ax) Term.bot

namespace Consistent

variable {Ax Ax₁ Ax₂ : AxiomSet Sig}

/-- What a consistent set entails is consistent. -/
theorem of_entails (e : Ax₁ ⟹ Ax₂) (h : Consistent Ax₁) : Consistent Ax₂ :=
  fun hb => h (Derivable.cut e hb)

theorem mono (hs : Ax₂ ⊆ Ax₁) (h : Consistent Ax₁) : Consistent Ax₂ :=
  of_entails (Entails.of_subset hs) h

theorem union_left (h : Consistent (Ax₁ ∪ Ax₂)) : Consistent Ax₁ := mono (subset_union_left _ _) h
theorem union_right (h : Consistent (Ax₁ ∪ Ax₂)) : Consistent Ax₂ := mono (subset_union_right _ _) h

/-- The form the schemas relative to the empty theory take. -/
theorem empty_union (h : Consistent Ax) : Consistent (empty ∪ Ax) :=
  mono (fun _ ha => ha.elim (fun h => h.elim) id) h

end Consistent

/-! The two directions between consistency and non-theoremhood, which the side conditions
of Distinctness and Possibility need: a sentence whose negation is consistent with the
theory is not its theorem; and a sentence that is not a theorem has a consistent negation,
by the deduction theorem and excluded middle. -/

variable {Ax : AxiomSet Sig} {p : Sentence Sig}

theorem not_theorem_of_consistent_neg (h : Consistent (Ax ∪ single (Term.neg p))) :
    ¬ Theorem (C.axioms ∪ Ax) p :=
  fun hp => h (Derivable.notE (Derivable.mono (fun _ hb => hb.elim Or.inl (fun h => Or.inr (Or.inl h))) hp)
    (Theorem.ax (Or.inr rfl)))

theorem consistent_neg_of_not_theorem (h : ¬ Theorem (C.axioms ∪ Ax) p) :
    Consistent (Ax ∪ single (Term.neg p)) :=
  fun hb => h (Derivable.orE (Derivable.em p) Derivable.hyp₀
    (Derivable.botE (Derivable.impE (Derivable.weaken₁ (Theorem.deductionC hb)) Derivable.hyp₀)))

/-- `C⁻ ⊢ A → ¬B` makes `A` and `B` together inconsistent: the form in which the
translator derives a record concluding `False`. -/
theorem not_consistent_of_imp_neg {A B : Sentence Sig}
    (h : C.TheoremMinus (Term.imp A (Term.neg B))) : ¬ Consistent (single A ∪ single B) :=
  fun hc => hc (Derivable.notE (Theorem.ax (Or.inr rfl))
    (Theorem.mp (Theorem.ofCMinus h) (Theorem.ax (Or.inl rfl))))

/-- What implies a refutable sentence is refutable: if `C ⊢ A → B` and `¬B` is consistent,
so is `¬A`. -/
theorem consistent_neg_of_imp {A B : Sentence Sig} (h : C.Theorem (Term.imp A B))
    (hB : Consistent (single (Term.neg B))) : Consistent (single (Term.neg A)) :=
  Consistent.mono (subset_union_right _ _) (consistent_neg_of_not_theorem (Ax := empty) fun hA =>
    not_theorem_of_consistent_neg (Consistent.empty_union hB) (Theorem.mp (Theorem.ofC h) hA))

/-- A sentence consistent with the theory is not provably `⊥`: the non-theoremhood that
Distinctness needs for `¬(P = ⊥)`, which is `◇P`. -/
theorem not_theorem_eq_bot_of_consistent (h : Consistent (Ax ∪ single p)) :
    ¬ Theorem (C.axioms ∪ Ax) (Term.eq' p Term.bot) :=
  fun he => h (Derivable.eqMp (Derivable.mono (fun _ hb => hb.elim Or.inl (fun h => Or.inr (Or.inl h))) he)
    (Theorem.ax (Or.inr rfl)))

end AxiomSet

end Classicism.Meta
