import Classicism.Models.OldNewPredicates

/-!
# The concrete IC and RC failures

Source: old-new-boolean-completeness-and-rigidity-separation.md, the corrected
IC argument (unpaginated). Original Lean submission, misc, 22 October 2026.
The separate future-BC module belongs to the delegated independent author.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory
noncomputable section

/-- The semantic clause for strong inextensibility at the root. -/
def ICData (Y : RelDom E et) : Prop :=
  ∀ {V : cat.Ob} (k : E ⟶ V) (Z : RelDom V et),
    (∀ a : Tup et V, profile Y k a → ∀ {U : cat.Ob} (j : V ⟶ U),
      profile Z j (Args.map model.inner et j a)) →
    ∀ {U : cat.Ob} (j : V ⟶ U) (a : Tup et U),
      profile Y (k ≫ j) a → profile Z j a

theorem holds_ic_iff : model.HoldsSentence (P.InextensibleComprehension.quoted et) ↔
    ∀ X : RelDom E et, ∃ Y : RelDom E et, ICData Y ∧
      ∀ a : Tup et E, profile X (𝟙 E) a ↔ profile Y (𝟙 E) a := by
  simp only [Premodel.HoldsSentence, P.InextensibleComprehension.quoted,
    model.holds_forall isModel, model.holds_exists isModel, model.holds_conj isModel,
    model.holds_box isModel, model.holds_imp isModel, Premodel.holds_inclR isModel,
    Premodel.holds_coextR isModel, Premodel.sem_boxR isModel, Premodel.sem_var,
    IEnv.get, IEnv.get_map, model.incl_map, Intension.mem_map, Set.mem_ofPred_eq,
    Category.comp_id, Category.id_comp, ICData, profile]
  rfl

/-- Universality at E propagates to every arrow returning to E by finite
approximation with a permutation. No persistence premise is assumed. -/
theorem universal_return (Y : RelDom E et)
    (hu : ∀ x : Nat, profile Y (𝟙 E) (x, PUnit.unit))
    (h : E ⟶ E) (x : Nat) : profile Y h (x, PUnit.unit) := by
  obtain ⟨S, hS, hp⟩ := SymBase.finPinned (S := base) (.rel et) Y
  obtain ⟨g, hg, hag⟩ := approximate h hS
  obtain ⟨gi, _, _, hgi⟩ := syms_inv E g hg
  apply (profile_approx hp hg hgi hag (x, PUnit.unit)).2
  exact hu (FunCat.fn gi x)

theorem no_universal_ICData (Y : RelDom E et)
    (hu : ∀ x : Nat, profile Y (𝟙 E) (x, PUnit.unit)) : ¬ ICData Y := by
  intro hi
  have root_old : ∀ {V : cat.Ob} (h : E ⟶ V) (a : Tup et V),
      profile Y h a → old V a.1 := by
    have hpre : ∀ a : Tup et E, profile Y (𝟙 E) a → ∀ {U : cat.Ob} (j : E ⟶ U),
        profile (oldEntity E) j (Args.map model.inner et j a) := by
      intro a _ U j
      apply (profile_old j _).2
      change old U (FunCat.fn j a.1)
      cases U
      · trivial
      · exact j.2.2 a.1
    intro V h a ha
    exact (profile_old h a).1 (hi (𝟙 E) (oldEntity E) hpre h a (by simpa using ha))
  let b : X O := Sum.inr 0
  have hpreO : ∀ a : Tup et O, profile Y (canon O) a → ∀ {U : cat.Ob} (j : O ⟶ U),
      profile (avoidEntity O b) j (Args.map model.inner et j a) := by
    intro a ha U j
    apply (profile_avoid b j _).2
    change FunCat.fn j a.1 ≠ FunCat.fn j b
    intro he
    have hx := j.2.1 he
    have ho := root_old (canon O) a ha
    rw [hx] at ho
    exact ho
  have hreturn : profile Y (canon O ≫ back) (FunCat.fn back b, PUnit.unit) :=
    universal_return Y hu (canon O ≫ back) (FunCat.fn back b)
  have hbad := hi (canon O) (avoidEntity O b) hpreO back (FunCat.fn back b, PUnit.unit) hreturn
  exact ((profile_avoid b back _).1 hbad) rfl

theorem not_ic_et : ¬ model.HoldsSentence (P.InextensibleComprehension.quoted et) := by
  intro h
  obtain ⟨Y, hi, hco⟩ := holds_ic_iff.1 h (topEntity E)
  exact no_universal_ICData Y (fun x => (hco (x, PUnit.unit)).1 (profile_top _ _)) hi

/-- Unpack the official RC sentence and discard its persistence conjunct. -/
theorem rc_implies_ic : model.HoldsSentence (P.RigidComprehension.quoted et) →
    model.HoldsSentence (P.InextensibleComprehension.quoted et) := by
  intro h
  simp only [Premodel.HoldsSentence, P.RigidComprehension.quoted,
    P.InextensibleComprehension.quoted, model.holds_forall isModel,
    model.holds_exists isModel, model.holds_conj isModel] at h ⊢
  intro X
  obtain ⟨Y, hY, hco⟩ := h X
  exact ⟨Y, hY.2, hco⟩

theorem not_rc_et : ¬ model.HoldsSentence (P.RigidComprehension.quoted et) :=
  fun h => not_ic_et (rc_implies_ic h)


end
end Classicism.Meta.Intensional.OldNew
