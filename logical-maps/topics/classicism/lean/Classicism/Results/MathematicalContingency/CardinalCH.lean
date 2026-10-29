import Classicism.Results.MathematicalContingency.PairingTransport
import Classicism.Results.MathematicalContingency.CantorBernstein

/-!
The cardinal content of CH, independently of an ordered-field presentation.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The negative argument needs subsethood and two non-embeddings, not N into X.
All carriers and witnesses remain relational; no new choice or rigidity premise.
-/
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

def CardinalCH (N : α → Prop) (S : β → Prop) : Prop :=
  ∀ X : β → Prop, (∀ x, X x → S x) → Embeds X N ∨ Equinumerous X S

/-- A subset with the two obstruction properties refutes cardinal CH directly. -/
theorem not_cardinalCH_of_obstructions (N : α → Prop) (S X : β → Prop)
    (sub : ∀ x, X x → S x) (large : ¬ Embeds X N) (gap : ¬ Embeds S X) :
    ¬ CardinalCH N S := by
  intro h
  obtain small | ⟨F,hf⟩ := h X sub
  · exact large small
  · exact gap ⟨fun y x => F x y,(bijects_inverse X S F hf).1⟩

/-- Necessitation applies to the generic theorem, not to its local hypotheses. -/
theorem entailment_not_cardinalCH_of_obstructions (N : α → Prop) (S X : β → Prop)
    (P : Prop) (sub : □ (∀ x, X x → S x))
    (obstructions : EntailmentOrder P (¬ Embeds X N ∧ ¬ Embeds S X)) :
    EntailmentOrder P (¬ CardinalCH N S) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (hs : ∀ x, X x → S x)
      (h : P → ¬ Embeds X N ∧ ¬ Embeds S X) (hp : P) =>
      not_cardinalCH_of_obstructions N S X hs (h hp).1 (h hp).2)) sub) obstructions

/-- P need only be nonzero: actual truth of P is not assumed. -/
theorem possible_not_cardinalCH_of_obstructions (N : α → Prop) (S X : β → Prop)
    (P : Prop) (nonzero : P ≠ False) (sub : □ (∀ x, X x → S x))
    (obstructions : EntailmentOrder P (¬ Embeds X N ∧ ¬ Embeds S X)) :
    ◇ (¬ CardinalCH N S) :=
  dia_mono P (¬ CardinalCH N S)
    (entailment_not_cardinalCH_of_obstructions N S X P sub obstructions) nonzero

/-- Transfer CH using only an embedding of the new continuum into the old one
and an embedding of the old countability carrier into the new one. -/
theorem cardinalCH_of_embeddings (N : α → Prop) (M : β → Prop)
    (S : γ → Prop) (R : δ → Prop) (ch : CardinalCH N S)
    (continuum : Embeds R S) (naturals : Embeds N M) : CardinalCH M R := by
  obtain ⟨F,hf⟩ := continuum
  intro X sub
  let G : δ → γ → Prop := fun x y => X x ∧ F x y
  have hg : Injects G X S :=
    ⟨⟨fun x y h => ⟨h.1,(hf.1.1 x y h.2).2⟩,
      fun x hx => (hf.1.2.1 x (sub x hx)).elim
        (fun y hy => ⟨y,hy.1,hx,hy.2⟩),
      fun x y z hy hz => hf.1.2.2 x y z hy.2 hz.2⟩,
      fun x z y hx hz => hf.2 x z y hx.2 hz.2⟩
  have hb := injects_bijects_image X S G hg
  have forward : Embeds X (RelImage G) := ⟨G,hb.1⟩
  have backward : Embeds (RelImage G) X :=
    ⟨fun y x => G x y,(bijects_inverse X (RelImage G) G hb).1⟩
  obtain small | ⟨J,hj⟩ := ch (RelImage G) (image_subset G X S hg.1)
  · exact Or.inl (embeds_trans X N M
      (embeds_trans X (RelImage G) N forward small) naturals)
  · have reverse : Embeds S (RelImage G) :=
      ⟨fun y x => J x y,(bijects_inverse (RelImage G) S J hj).1⟩
    exact Or.inr (cantor_bernstein X R (embeds_of_subset X R sub)
      (embeds_trans R (RelImage G) X
        (embeds_trans R S (RelImage G) ⟨F,hf⟩ reverse) backward))

/-- The negative direction needs the opposite pair of embeddings, not bijections. -/
theorem not_cardinalCH_of_embeddings (N : α → Prop) (M : β → Prop)
    (S : γ → Prop) (R : δ → Prop) (notCH : ¬ CardinalCH N S)
    (continuum : Embeds S R) (naturals : Embeds M N) : ¬ CardinalCH M R :=
  fun h => notCH (cardinalCH_of_embeddings M N R S h continuum naturals)

#classicism_check not_cardinalCH_of_obstructions entailment_not_cardinalCH_of_obstructions possible_not_cardinalCH_of_obstructions cardinalCH_of_embeddings not_cardinalCH_of_embeddings
#classicism_types not_cardinalCH_of_obstructions entailment_not_cardinalCH_of_obstructions possible_not_cardinalCH_of_obstructions cardinalCH_of_embeddings not_cardinalCH_of_embeddings
end Classicism.MathematicalContingency
