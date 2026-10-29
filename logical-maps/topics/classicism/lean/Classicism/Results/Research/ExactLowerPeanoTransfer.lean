import Classicism.Results.Research.ExactLowerCorrespondence

/-!
# Removing the exact-Peano hypothesis

An exact finite cardinality determines its at-least partner by upward
closure under subproperties. The synchronous pairing is persistent, so
coextension of two partners upgrades to identity by Intensionality, not
by unrestricted propositional or functional extensionality.

Consequently even UNBOXED LowerPeano implies ExactPeano. Its boxed form
therefore suffices for the zero/successor-preserving bijection, with no
additional exact-Peano, choice, Barcan, or rigid-comprehension hypothesis.

Proof developed by GPT-6 Astra Pro, prompted by Andrew Bacon, 28 October 2026.
-/
namespace Classicism.ExactLower

variable {σ : Type} [Ty σ]

/-- A property contains a subproperty having exact cardinality q. -/
def UpwardCount (q : (σ → Prop) → Prop) (X : σ → Prop) : Prop :=
  ∃ Y : σ → Prop, (∀ u, Y u → X u) ∧ q Y

/-- The synchronous pairing persists: induction uses only necessitations
of its closed zero and successor introduction theorems. -/
theorem exactLowerPair_persistent (q l : (σ → Prop) → Prop)
    (h : ExactLowerPair q l) : □ (ExactLowerPair q l) :=
  h (fun x y => □ (ExactLowerPair x y))
    ⟨nec% (@exactLowerPair_zero σ _),
      fun x y hxy => modal_K _ _ (nec% (exactLowerPair_suc x y)) hxy⟩

/-- The at-least partner is coextensive with the upward closure of the
exact count. This uses no Peano assumption. -/
theorem exactLowerPair_upward (q l : (σ → Prop) → Prop)
    (h : ExactLowerPair q l) : ∀ X, l X ↔ UpwardCount q X := by
  have hh := h (fun x y => ExactLowerPair x y ∧
      ∀ X, y X ↔ UpwardCount x X)
    ⟨⟨exactLowerPair_zero, by
        intro X
        constructor
        · intro _
          exact ⟨(fun _ => False), (fun _ hf => hf.elim), (fun _ hf => hf)⟩
        · intro _
          trivial⟩,
      by
        intro x y ih
        refine ⟨exactLowerPair_suc x y ih.1, ?_⟩
        intro X
        constructor
        · intro hs
          rcases hs with ⟨a, ha, hy⟩
          rcases (ih.2 (fun u => X u ∧ u ≠ a)).mp hy with ⟨Y, hYX, hxY⟩
          refine ⟨(fun u => Y u ∨ u = a), ?_, a, Or.inr rfl, ?_⟩
          · intro u hu
            exact hu.elim (fun hYu => (hYX u hYu).1) (fun hua => hua.symm ▸ ha)
          · exact finiteCardinality_coext x (exactLowerPair_exact x y ih.1)
              Y (fun u => (Y u ∨ u = a) ∧ u ≠ a) hxY
              (fun u => ⟨fun hYu => ⟨Or.inl hYu, (hYX u hYu).2⟩,
                fun hu => hu.1.elim (fun hYu => hYu)
                  (fun hua => False.elim (hu.2 hua))⟩)
        · intro hs
          rcases hs with ⟨Y, hYX, a, ha, hx⟩
          refine ⟨a, hYX a ha, (ih.2 (fun u => X u ∧ u ≠ a)).mpr ?_⟩
          exact ⟨(fun u => Y u ∧ u ≠ a),
            (fun u hu => ⟨hYX u hu.1, hu.2⟩), hx⟩⟩
  exact hh.2

/-- Two at-least partners of the same exact count are coextensive. -/
theorem exactLowerPair_coext (q l l' : (σ → Prop) → Prop)
    (h : ExactLowerPair q l) (h' : ExactLowerPair q l') :
    ∀ X, l X ↔ l' X :=
  fun X => (exactLowerPair_upward q l h X).trans
    (exactLowerPair_upward q l' h' X).symm

/-- Functionality needs no Peano assumption. Persist both pairing facts,
necessitate the closed coextension theorem, then use Intensionality. -/
theorem exactLowerPair_right_unique_unconditional
    (q l : (σ → Prop) → Prop) (h : ExactLowerPair q l) :
    ∀ l', ExactLowerPair q l' → l' = l := by
  intro l' h'
  apply intensionality l' l
  exact modal_K _ _
    (modal_K _ _ (nec% (exactLowerPair_coext q l' l))
      (exactLowerPair_persistent q l' h'))
    (exactLowerPair_persistent q l h)

/-- Exact zero is never a successor, even without finiteness: evaluate
both sides on the empty property. -/
theorem exactZero_ne_suc (q : (σ → Prop) → Prop) :
    ZeroCard σ ≠ SucCard q := by
  intro heq
  have hs : SucCard q (fun _ : σ => False) :=
    (congrFun heq (fun _ : σ => False)).mp (fun _ hf => hf)
  rcases hs with ⟨a, ha, _⟩
  exact ha

/-- No extra exact-Peano assumption is needed; unboxed lower-Peano
already transfers across the synchronous pairing. -/
theorem exactPeano_of_lowerPeano (hp : LowerPeano σ) : ExactPeano σ := by
  refine ⟨(fun q _ => exactZero_ne_suc q), ?_⟩
  intro m n hm hn hsucc
  obtain ⟨l, hml⟩ := exactLowerPair_total_exact m hm
  obtain ⟨k, hnk⟩ := exactLowerPair_total_exact n hn
  have hsnk : ExactLowerPair (SucCard m) (SucCard k) :=
    hsucc.symm ▸ exactLowerPair_suc n k hnk
  have hkl : SucCard k = SucCard l :=
    exactLowerPair_right_unique_unconditional (SucCard m) (SucCard l)
      (exactLowerPair_suc m l hml) (SucCard k) hsnk
  have hbase : k = l := hp.2 k l
    (exactLowerPair_lower n k hnk) (exactLowerPair_lower m l hml) hkl
  have hnl : ExactLowerPair n l := hbase ▸ hnk
  exact (exactLowerPair_left_unique hp m l hml n hnl).symm

/-- The zero/successor-preserving relational bijection from lower-Peano
alone. The earlier two-premise theorem remains available unchanged. -/
theorem exactLowerBijection_of_lowerPeano (hp : LowerPeano σ) :
    ExactLowerBijection σ :=
  exactLowerBijection_of_peano (exactPeano_of_lowerPeano hp) hp

/-- The CH project's necessary lower-Peano condition implies exact-Peano. -/
theorem exactPeano_of_box_lowerPeano (hp : □ (LowerPeano σ)) :
    ExactPeano σ := exactPeano_of_lowerPeano (box_elim hp)

/-- It also implies NECESSARY exact-Peano, by K. -/
theorem necessaryExactPeano_of_box_lowerPeano (hp : □ (LowerPeano σ)) :
    □ (ExactPeano σ) :=
  modal_K _ _ (nec% (@exactPeano_of_lowerPeano σ _)) hp

/-- Single-premise correspondence theorem for the original CH setting. -/
theorem exactLowerBijection_of_box_lowerPeano (hp : □ (LowerPeano σ)) :
    ExactLowerBijection σ := exactLowerBijection_of_lowerPeano (box_elim hp)

/-- Necessarily there is such a bijection; no fixed rigid graph is asserted. -/
theorem necessaryExactLowerBijection_of_box_lowerPeano
    (hp : □ (LowerPeano σ)) : □ (ExactLowerBijection σ) :=
  modal_K _ _ (nec% (@exactLowerBijection_of_lowerPeano σ _)) hp

#classicism_check exactLowerPair_persistent exactLowerPair_upward
  exactLowerPair_coext exactLowerPair_right_unique_unconditional exactZero_ne_suc
  exactPeano_of_lowerPeano exactLowerBijection_of_lowerPeano
  exactPeano_of_box_lowerPeano necessaryExactPeano_of_box_lowerPeano
  exactLowerBijection_of_box_lowerPeano necessaryExactLowerBijection_of_box_lowerPeano
#classicism_types exactLowerPair_persistent exactLowerPair_upward
  exactLowerPair_coext exactLowerPair_right_unique_unconditional exactZero_ne_suc
  exactPeano_of_lowerPeano exactLowerBijection_of_lowerPeano
  exactPeano_of_box_lowerPeano necessaryExactPeano_of_box_lowerPeano
  exactLowerBijection_of_box_lowerPeano necessaryExactLowerBijection_of_box_lowerPeano

end Classicism.ExactLower
