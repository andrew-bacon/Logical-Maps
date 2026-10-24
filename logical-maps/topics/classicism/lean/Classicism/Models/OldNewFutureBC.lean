import Classicism.Models.OldNewPredicates

/-!
# Boolean Completeness fails at the old/new future object

Original formalization (misc), 23 October 2026. Direct mathematical source:
research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md,
sections "Failure of BC at O" and "No least upper bound" (unpaginated).

We prove the Boolean-dual greatest-lower-bound argument for the genuinely
admitted family of complements of the old individual haecceities. Every
new haecceity is a lower bound. A finite pin for an alleged greatest lower
bound cannot distinguish a fresh new individual from a fresh old one after
an allowed return arrow. No external even-haecceity family is used.

This module's source has not been independently compiled by its author;
formal verification is the responsibility of the serial integrator.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory
noncomputable section

/-- Actual membership in the admitted old anti-haecceity family. -/
def futureFamilyMember (A : RelDom O et) : Prop :=
  profile (oldAvoidFamily O) (𝟙 O) (A, PUnit.unit)

theorem futureFamilyMember_iff (A : RelDom O et) :
    futureFamilyMember A ↔ ∃ x : X O, old O x ∧ A = avoidEntity O x := by
  unfold futureFamilyMember profile
  rw [incl_oldAvoid]
  rfl

/-- Modify the image of a fresh point while retaining a prescribed finite
pin. The resulting map is an actual allowed O-to-E arrow. -/
theorem future_return_hit {S : Set (X O)} (hS : S.Finite)
    {a b : X O} (ha : a ∉ S) (hb : b ∉ S) :
    ∃ j : O ⟶ E, AgreeOn cat.De S back j ∧
      FunCat.fn j a = FunCat.fn back b := by
  classical
  let q : X O → Nat := fun x => if x = a then FunCat.fn back b else FunCat.fn back x
  have hq : Set.InjOn q (S ∪ {a}) := by
    intro x hx y hy hxy
    by_cases hxa : x = a
    · by_cases hya : y = a
      · exact hxa.trans hya.symm
      · have hyS : y ∈ S := by
          rcases hy with hyS | hyA
          · exact hyS
          · exact False.elim (hya hyA)
        have he : FunCat.fn back b = FunCat.fn back y := by
          simpa only [q, hxa, if_pos rfl, if_neg hya] using hxy
        have hby : b = y := back.2.1 he
        exact False.elim (hb (hby.symm ▸ hyS))
    · by_cases hya : y = a
      · have hxS : x ∈ S := by
          rcases hx with hxS | hxA
          · exact hxS
          · exact False.elim (hxa hxA)
        have he : FunCat.fn back x = FunCat.fn back b := by
          simpa only [q, hya, if_neg hxa, if_pos rfl] using hxy
        have hxb : x = b := back.2.1 he
        exact False.elim (hb (hxb ▸ hxS))
      · apply back.2.1
        simpa only [q, if_neg hxa, if_neg hya] using hxy
  obtain ⟨e, he⟩ := extend_finite (W := O) (V := E)
    (hS.union (Set.finite_singleton a)) q hq
  let j : O ⟶ E := FunCat.arr e ⟨e.injective, trivial⟩
  refine ⟨j, ?_, ?_⟩
  · intro x hx
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    change FunCat.fn back x = e x
    symm
    simpa only [q, if_neg hxa] using he x (Or.inl hx)
  · change e a = FunCat.fn back b
    simpa only [q, if_pos rfl] using he a (Or.inr rfl)

/-- The represented family at O has no greatest lower bound under the
actual intensional order. This is not an unrepresented external family. -/
theorem future_old_antihaecceities_no_glb :
    ¬ ∃ L : RelDom O et, ∀ z : RelDom O et,
      (∀ A : RelDom O et, futureFamilyMember A →
        model.incl et O z ⊆ model.incl et O A) ↔
      model.incl et O z ⊆ model.incl et O L := by
  rintro ⟨L, hL⟩
  obtain ⟨S, hS, hp⟩ := symIdeal_inner_finPinned
    (De := cat.De) (G := syms) (J := PinIdeal.fin cat.De) (W₀ := E)
    (nonempty_e := base.ne) (I := model.I) (.rel et) O L
  let label : X O → Nat := Sum.elim id id
  obtain ⟨n, hn⟩ := (hS.image label).exists_notMem
  let a : X O := Sum.inl n
  let b : X O := Sum.inr n
  have ha : a ∉ S := fun hs => hn ⟨a, hs, rfl⟩
  have hb : b ∉ S := fun hs => hn ⟨b, hs, rfl⟩
  have hbold : ¬ old O b := fun h => h
  have hpointLower : ∀ A : RelDom O et, futureFamilyMember A →
      model.incl et O (pointEntity O b) ⊆ model.incl et O A := by
    intro A hA
    obtain ⟨x, hx, rfl⟩ := (futureFamilyMember_iff A).1 hA
    apply point_below_avoid
    intro hbx
    exact hbold (hbx.symm ▸ hx)
  have hpoint : model.incl et O (pointEntity O b) ⊆ model.incl et O L :=
    (hL (pointEntity O b)).1 hpointLower
  have hLb : profile L back (FunCat.fn back b, PUnit.unit) := by
    apply hpoint
    exact (profile_point b back (FunCat.fn back b, PUnit.unit)).2 rfl
  obtain ⟨j, hj, hja⟩ := future_return_hit hS ha hb
  have hLbj : profile L j (FunCat.fn back b, PUnit.unit) :=
    (pinned_profile_at hp hj (FunCat.fn back b, PUnit.unit)).1 hLb
  have hLower : ∀ A : RelDom O et, futureFamilyMember A →
      model.incl et O L ⊆ model.incl et O A :=
    (hL L).2 (fun _ h => h)
  have haMember : futureFamilyMember (avoidEntity O a) :=
    (futureFamilyMember_iff _).2 ⟨a, trivial, rfl⟩
  have hAvoid : profile (avoidEntity O a) j (FunCat.fn back b, PUnit.unit) :=
    hLower _ haMember hLbj
  exact ((profile_avoid a j (FunCat.fn back b, PUnit.unit)).1 hAvoid) hja.symm

/-- The official BC_et instance is false at every arrow whose target is O. -/
theorem future_not_bc_et (k : E ⟶ O) :
    ¬ model.Holds k (P.BooleanCompleteness.quoted et) .nil := by
  intro hBC
  change model.Holds k (Sentence.bc et) .nil at hBC
  obtain ⟨L, hL⟩ := (model.holds_bc_iff isModel et k).1 hBC (oldAvoidFamily O)
  apply future_old_antihaecceities_no_glb
  exact ⟨L, hL⟩

/-- Positive semantic formulation of the refutation, using the actual
quoted BC instance in the fixed object language. -/
theorem future_holds_not_bc_et (k : E ⟶ O) :
    model.Holds k (Term.neg (P.BooleanCompleteness.quoted et)) .nil :=
  (model.holds_neg isModel k .nil _).2 (future_not_bc_et k)

/-- Consequently BC_et is not necessary at the original root E. -/
theorem root_not_box_bc_et :
    ¬ model.HoldsSentence (Term.box (P.BooleanCompleteness.quoted et)) := by
  intro hBC
  have hO := (model.holds_box isModel (𝟙 E)
    (P.BooleanCompleteness.quoted et) .nil).1 hBC (canon O)
  change model.Holds (canon O) (P.BooleanCompleteness.quoted et)
    (model.push (canon O) IEnv.nil) at hO
  exact future_not_bc_et (canon O)
    (Eq.mp (congrArg (model.Holds (canon O) (P.BooleanCompleteness.quoted et))
      (IEnv.nil_eq (model.push (canon O) IEnv.nil))) hO)

end
end Classicism.Meta.Intensional.OldNew
