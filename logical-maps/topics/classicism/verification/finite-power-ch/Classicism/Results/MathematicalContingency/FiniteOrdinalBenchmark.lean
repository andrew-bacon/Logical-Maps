import Classicism.Results.MathematicalContingency.OrdinalCardinalityShadow
import Classicism.Results.MathematicalContingency.NaturalRecursion

/-! A uniform relational injection from LowerNat into the inexact ordinal carrier.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026.
No actual individual infinity, RC, choice, or exact-ordinal substitution is used.
-/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def FiniteOrdinalRun : ((σ → Prop) → Prop) → OrdinalCarrier σ → Prop :=
  NatRun (fun _ α β => β = OrdSuc α) (OrdZero σ)

theorem finiteOrdinalRun_shadow (n : (σ → Prop) → Prop) (α : OrdinalCarrier σ)
    (h : FiniteOrdinalRun n α) : Ordinal α ∧ n = OrdinalCard α := by
  apply h (fun n α => Ordinal α ∧ n = OrdinalCard α)
  · exact ⟨ordinal_zero,ordinalCard_zero.symm⟩
  · intro i β γ _ ih step
    subst γ
    exact ⟨ordinal_suc β ih.1,(congrArg SucCard ih.2).trans (ordinalCard_suc β ih.1).symm⟩

theorem finiteOrdinalRun_maps (hp : LowerPeano σ) :
    Maps (@FiniteOrdinalRun σ _) LowerNat Ordinal :=
  natRun_maps hp Ordinal (fun _ α β => β = OrdSuc α) (OrdZero σ) ordinal_zero
    (fun _ α β _ hα e => e.symm ▸ ordinal_suc α hα)
    (fun _ α _ hα => ⟨OrdSuc α,ordinal_suc α hα,rfl⟩)
    (fun _ _ _ _ _ h k => h.trans k.symm)

theorem finiteOrdinalRun_injective (n m : (σ → Prop) → Prop) (α : OrdinalCarrier σ)
    (hn : FiniteOrdinalRun n α) (hm : FiniteOrdinalRun m α) : n = m :=
  (finiteOrdinalRun_shadow n α hn).2.trans (finiteOrdinalRun_shadow m α hm).2.symm

theorem lowerNat_embeds_ordinal (hp : LowerPeano σ) : Embeds (@LowerNat σ _) (@Ordinal σ _) :=
  ⟨FiniteOrdinalRun,finiteOrdinalRun_maps hp,finiteOrdinalRun_injective⟩

#classicism_check finiteOrdinalRun_shadow finiteOrdinalRun_maps finiteOrdinalRun_injective lowerNat_embeds_ordinal
#classicism_types finiteOrdinalRun_shadow finiteOrdinalRun_maps finiteOrdinalRun_injective lowerNat_embeds_ordinal
end Classicism.MathematicalContingency
