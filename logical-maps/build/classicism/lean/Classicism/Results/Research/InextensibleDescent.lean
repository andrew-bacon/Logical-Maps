import Classicism.Results.Research.InextensiblePower
import Classicism.Results.Research.ModalPropagation

/-!
# Inextensible comprehension descends one property type

Target: the local descent in §5 of
`research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md`.
This proof uses haecceity pullback instead of the source's union construction.
The source's argument is unchanged. The closed pullback lemma comes from the
separately audited `ModalPropagation` module. Direct source of this adaptation:
original research, `misc`, 22 October 2026; no publication attribution.
-/

namespace Classicism.Research.InextensiblePower
open Classicism.Paper Classicism.P Classicism.Research.ModalPropagation

theorem codes_from_lift {σ : Type} [Ty σ] (X : σ → Prop)
    (G : (σ → Prop) → Prop) (hc : Lift X ≡ G) :
    ∀ H, G H → IsCode H :=
  fun H hH => ((hc H).2 hH).elim fun a ha => ⟨a, ha.1⟩

theorem pullback_coext {σ : Type} [Ty σ] (X : σ → Prop)
    (G : (σ → Prop) → Prop) (hc : Lift X ≡ G) : X ≡ Pullback G :=
  fun a => (lift_on_code X a).symm.trans (hc (Haecceity a))

theorem inextensible_pullback_of_codes {σ : Type} [Ty σ]
    (G : (σ → Prop) → Prop) (hg : Inextensible G)
    (hc : ∀ H, G H → IsCode H) : Inextensible (Pullback G) :=
  have hseal : □ (∀ H, G H → IsCode H) :=
    (weaklyInextensible_of_inextensible hg) IsCode
      (fun H hH => code_necessary H (hc H hH))
  modal_K _ _ (modal_K _ _ (nec% (pullback_weakly_inextensible G)) hg) hseal

theorem ic_descends {σ : Type} [Ty σ] :
    InextensibleComprehension ((σ → Prop) → Prop) →
    InextensibleComprehension (σ → Prop) :=
  fun ic X => (ic (Lift X)).elim fun G hG =>
    ⟨Pullback G, inextensible_pullback_of_codes G hG.1 (codes_from_lift X G hG.2),
      pullback_coext X G hG.2⟩

theorem weak_ic_descends {σ : Type} [Ty σ] :
    WeaklyInextensibleComprehension ((σ → Prop) → Prop) →
    WeaklyInextensibleComprehension (σ → Prop) :=
  fun ic X => (ic (Lift X)).elim fun G hG =>
    ⟨Pullback G, pullback_weakly_inextensible G hG.1 (codes_from_lift X G hG.2),
      pullback_coext X G hG.2⟩

theorem nd_higher_ic_tame {σ : Type} [Ty σ] :
    NecessityOfDistinctness Prop → InextensibleComprehension ((σ → Prop) → Prop) →
    TameRigidity (σ → Prop) := fun nd ic => nd_ic_tame nd (ic_descends ic)

end Classicism.Research.InextensiblePower
