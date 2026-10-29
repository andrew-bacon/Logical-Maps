import Classicism.Results.MathematicalContingency.RepresentativeFibres
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β : Type} [Ty α] [Ty β]

/-- Values through rigid representatives on both sides of an injection. -/
def PowerRepresentativeValue (Q : Prop) (J : (α → Prop) → (β → Prop) → Prop)
    (X : α → Prop) (Y : β → Prop) : Prop :=
  Q ∧ ∃ U V, Rigid U ∧ Rigid V ∧ U ≡ X ∧ V ≡ Y ∧ J U V

theorem powerRepresentativeValue_cover_current (A : α → Prop) (E : (β → Prop) → Prop)
    (Q : Prop) (J : (α → Prop) → (β → Prop) → Prop) (X : α → Prop)
    (hr : ∃ U, Rigid U ∧ U ≡ X)
    (hs : Q → ∀ a, X a → A a)
    (hj : Q → Injects J (RigidPower A) (RepresentativeImage E)) (hq : Q) :
    ∃ Y, E Y ∧ PowerRepresentativeValue Q J X Y := by
  obtain ⟨U,hu,hUX⟩ := hr
  obtain ⟨V,hv,hJ⟩ := (hj hq).1.2.1 U ⟨hu,fun a ha => hs hq a ((hUX a).mp ha)⟩
  obtain ⟨Y,hY,hVY⟩ := hv.2
  exact ⟨Y,hY,hq,U,V,hu,hv.1,hUX,hVY,hJ⟩

theorem powerRepresentativeValue_cover (A : α → Prop) (E : (β → Prop) → Prop)
    (Q : Prop) (J : (α → Prop) → (β → Prop) → Prop) (X : α → Prop)
    (rc : □ (Classicism.P.RigidComprehension (α → Prop)))
    (hs : EntailmentOrder Q (∀ a, X a → A a))
    (hj : EntailmentOrder Q (Injects J (RigidPower A) (RepresentativeImage E))) :
    EntailmentOrder Q (∃ Y, E Y ∧ PowerRepresentativeValue Q J X Y) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (powerRepresentativeValue_cover_current A E Q J X))
    (modal_K _ _ (nec% (fun h => rigid_representative_exists h X)) rc)) hs) hj

theorem powerRepresentativeValue_conflict (A : α → Prop) (E : (β → Prop) → Prop)
    (Q : Prop) (J : (α → Prop) → (β → Prop) → Prop) (X Z : α → Prop) (Y : β → Prop)
    (hj : Q → Injects J (RigidPower A) (RepresentativeImage E)) (hs : Q → ¬ (X ≡ Z))
    (hx : PowerRepresentativeValue Q J X Y) (hz : PowerRepresentativeValue Q J Z Y) : False := by
  obtain ⟨U,V,hu,hv,hUX,hVY,hUV⟩ := hx.2
  obtain ⟨W,T,hw,ht,hWZ,hTY,hWT⟩ := hz.2
  have e : V = T := rigid_eq_of_coext V T hv ht (fun b => (hVY b).trans (hTY b).symm)
  have hWV : J W V := e.symm ▸ hWT
  have k : U = W := (hj hx.1).2 U W V hUV hWV
  have hUZ : U ≡ Z := k.symm ▸ hWZ
  exact hs hx.1 (fun a => (hUX a).symm.trans (hUZ a))

theorem powerRepresentativeValue_disjoint (A : α → Prop) (E : (β → Prop) → Prop)
    (Q : Prop) (J : (α → Prop) → (β → Prop) → Prop) (X Z : α → Prop) (Y : β → Prop)
    (hj : EntailmentOrder Q (Injects J (RigidPower A) (RepresentativeImage E)))
    (hs : EntailmentOrder Q (¬ (X ≡ Z))) :
    □ (¬ (PowerRepresentativeValue Q J X Y ∧ PowerRepresentativeValue Q J Z Y)) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun hj hs h => powerRepresentativeValue_conflict A E Q J X Z Y hj hs h.1 h.2)) hj) hs

theorem powerRepresentativeValue_below (P Q : Prop) (J : (α → Prop) → (β → Prop) → Prop)
    (hQP : EntailmentOrder Q P) (X : α → Prop) (Y : β → Prop) :
    Below P (PowerRepresentativeValue Q J X Y) :=
  entailment_trans (PowerRepresentativeValue Q J X Y) Q P
    (nec% (fun h : PowerRepresentativeValue Q J X Y => h.1)) hQP

/-- A separated family of subsets obstructs an injection of the rigid power collection. -/
theorem rigidPower_representativeImage_no_injection
    (A : α → Prop) (D : (α → Prop) → Prop) (E : (β → Prop) → Prop) (P : Prop)
    (rc : □ (Classicism.P.RigidComprehension (α → Prop)))
    (ic : Classicism.P.IntensionalChoice ((α → Prop) → (β → Prop) → Prop))
    (subsets : ∀ X, D X → EntailmentOrder P (∀ a, X a → A a))
    (separate : ∀ X Z, D X → D Z → X ≠ Z → EntailmentOrder P (¬ (X ≡ Z)))
    (obstruction : ∀ Q (V : (α → Prop) → (β → Prop) → Prop),
      (∀ X Y, D X → E Y → Below P (V X Y)) →
      (∀ X Z Y, D X → D Z → E Y → X ≠ Z → □ (¬ (V X Y ∧ V Z Y))) →
      (∀ X, D X → EntailmentOrder Q (∃ Y, E Y ∧ V X Y)) → Q = False) :
    EntailmentOrder P (¬ Embeds (RigidPower A) (RepresentativeImage E)) := by
  apply local_injection_exclusion (RigidPower A) (RepresentativeImage E) P ic
  intro Q hQP J hJ
  exact obstruction Q (PowerRepresentativeValue Q J)
    (fun X Y _ _ => powerRepresentativeValue_below P Q J hQP X Y)
    (fun X Z Y hX hZ _ hn => powerRepresentativeValue_disjoint A E Q J X Z Y hJ
      (entailment_trans Q P (¬ (X ≡ Z)) hQP (separate X Z hX hZ hn)))
    (fun X hX => powerRepresentativeValue_cover A E Q J X rc
      (entailment_trans Q P (∀ a, X a → A a) hQP (subsets X hX)) hJ)

#classicism_check powerRepresentativeValue_cover_current powerRepresentativeValue_cover powerRepresentativeValue_conflict powerRepresentativeValue_disjoint powerRepresentativeValue_below rigidPower_representativeImage_no_injection
#classicism_types powerRepresentativeValue_cover_current powerRepresentativeValue_cover powerRepresentativeValue_conflict powerRepresentativeValue_disjoint powerRepresentativeValue_below rigidPower_representativeImage_no_injection
end Classicism.MathematicalContingency
