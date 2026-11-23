import Classicism.Results.MathematicalContingency.Definitions
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem

/-!
Reusable modal lemmas for Andrew Bacon's CH project.
Formalization: OpenAI Codex, prompted by Andrew Bacon, 24 October 2026.
All optional principles remain explicit hypotheses. No functional choice is used.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper

/-- Coextensive rigid relations are identical, at every relational arity. -/
theorem rigid_eq_of_coext {τ : Type} [Rel τ] [Pointwise τ]
    (A B : τ) (hA : Rigid A) (hB : Rigid B) (h : A ≡ B) : A = B := by
  have hab : □ (A ⊆ B) := box_elim hA.2 B
    (incl_trans A B (boxAt B) (incl_of_coext A B h) (box_elim hB.1))
  have hba : □ (B ⊆ A) := box_elim hB.2 A
    (incl_trans B A (boxAt A) (incl_of_coext' A B h) (box_elim hA.1))
  exact intensionality A B (modal_K _ _ (modal_K _ _
    (nec% (coext_of_incl A B)) hab) hba)

/-- Unique existence is relational; this does not introduce a representative function. -/
theorem rigid_representatives {τ : Type} [Rel τ] [Pointwise τ]
    (rc : P.RigidComprehension τ) (F : τ) :
    ∃ A, (Rigid A ∧ F ≡ A) ∧ ∀ B, (Rigid B ∧ F ≡ B) → B = A := by
  obtain ⟨A, hA, hFA⟩ := rc F
  refine ⟨A, ⟨hA, hFA⟩, ?_⟩
  intro B hB
  exact rigid_eq_of_coext B A hB.1 hA (coext_of_incl B A
    (incl_trans B F A (incl_of_coext' F B hB.2) (incl_of_coext F A hFA))
    (incl_trans A F B (incl_of_coext' F A hFA) (incl_of_coext F B hB.2)))

/-- Inextensibility suffices; persistence is not used. -/
theorem restricted_barcan {τ : Type} [Rel τ] (A F : τ)
    (hA : Inextensible A) (h : A ⊆ boxAt F) : □ (A ⊆ F) :=
  box_elim hA F h

theorem restricted_barcan_unary {σ : Type} [Ty σ] (A F : σ → Prop)
    (hA : Rigid A) (h : ∀ x, A x → □ (F x)) : □ (∀ x, A x → F x) :=
  restricted_barcan A F hA.2 h

theorem restricted_barcan_dual {σ : Type} [Ty σ] (A F : σ → Prop)
    (hA : Rigid A) (h : ◇ (∃ x, A x ∧ F x)) : ∃ x, A x ∧ ◇ (F x) := by
  refine (em (∃ x, A x ∧ ◇ (F x))).elim (fun he => he) ?_
  intro hn
  have hb : □ (∀ x, A x → ¬ F x) := restricted_barcan_unary A (fun x => ¬ F x) hA
    (fun x hx => box_not_of_not_dia _ (fun hd => hn ⟨x, hx, hd⟩))
  have hh : □ (¬ ∃ x, A x ∧ F x) := modal_K _ _
    (nec% (fun (ha : ∀ x, A x → ¬ F x) (he : ∃ x, A x ∧ F x) =>
      he.elim fun x hx => ha x hx.1 hx.2)) hb
  exact (not_dia_of_box_not _ hh h).elim

/-- Necessary invariance under current coextension; this is not identity invariance. -/
def CoextensionInvariant {τ : Type} [Rel τ] (Φ : τ → Prop) : Prop :=
  □ (∀ I J, I ≡ J → (Φ I ↔ Φ J))

/-- The pointwise union of a uniquely selected property is coextensive with it. -/
theorem selected_union {σ : Type} [Ty σ] (V : (σ → Prop) → Prop)
    (J : σ → Prop) (hj : V J) (hu : ∀ K, V K → K = J) :
    (fun x => ∃ K, V K ∧ K x) ≡ J := by
  intro x
  exact ⟨fun h => h.elim fun K hk => (hu K hk.1) ▸ hk.2,
    fun hx => ⟨J, hj, hx⟩⟩

theorem local_selection {σ : Type} [Ty σ]
    (ic : P.IntensionalChoice (σ → Prop)) (Q : Prop) (Φ : (σ → Prop) → Prop)
    (inv : CoextensionInvariant Φ) (hex : □ (Q → ∃ I, Φ I)) :
    ∃ I, □ (Q → Φ I) := by
  have total : □ (∃ I : σ → Prop, Q → Φ I) := modal_K _ _
    (nec% (fun (h : Q → ∃ I, Φ I) =>
      (em Q).elim
        (fun hq => (h hq).elim fun I hi => ⟨I, fun _ => hi⟩)
        (fun hn => ⟨fun _ => False, fun hq => (hn hq).elim⟩))) hex
  obtain ⟨V, hV, hu⟩ := ic (fun I => Q → Φ I) total
  have hv : □ (∀ I, V I → Q → Φ I) := (le_iff V _).mp hV
  refine ⟨fun x => ∃ I, V I ∧ I x, ?_⟩
  exact modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hi : ∀ I J, I ≡ J → (Φ I ↔ Φ J))
      (hs : ∀ I, V I → Q → Φ I)
      (he : ∃ J, V J ∧ ∀ K, V K → K = J) (hq : Q) =>
        he.elim fun J hj => (hi _ J (selected_union V J hj.1 hj.2)).mpr
          (hs J hj.1 hq))) inv) hv) hu

/-- The pointwise union of a uniquely selected property is coextensive with it. -/
theorem selected_union_binary {σ τ : Type} [Ty σ] [Ty τ] (V : (σ → τ → Prop) → Prop)
    (J : σ → τ → Prop) (hj : V J) (hu : ∀ K, V K → K = J) :
    (fun x y => ∃ K, V K ∧ K x y) ≡ J := by
  intro x y
  exact ⟨fun h => h.elim fun K hk => (hu K hk.1) ▸ hk.2,
    fun hx => ⟨J, hj, hx⟩⟩

theorem local_selection_binary {σ τ : Type} [Ty σ] [Ty τ]
    (ic : P.IntensionalChoice (σ → τ → Prop)) (Q : Prop) (Φ : (σ → τ → Prop) → Prop)
    (inv : CoextensionInvariant Φ) (hex : □ (Q → ∃ I, Φ I)) :
    ∃ I, □ (Q → Φ I) := by
  have total : □ (∃ I : σ → τ → Prop, Q → Φ I) := modal_K _ _
    (nec% (fun (h : Q → ∃ I, Φ I) =>
      (em Q).elim
        (fun hq => (h hq).elim fun I hi => ⟨I, fun _ => hi⟩)
        (fun hn => ⟨fun _ _ => False, fun hq => (hn hq).elim⟩))) hex
  obtain ⟨V, hV, hu⟩ := ic (fun I => Q → Φ I) total
  have hv : □ (∀ I, V I → Q → Φ I) := (le_iff V _).mp hV
  refine ⟨fun x y => ∃ I, V I ∧ I x y, ?_⟩
  exact modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hi : ∀ I J, I ≡ J → (Φ I ↔ Φ J))
      (hs : ∀ I, V I → Q → Φ I)
      (he : ∃ J, V J ∧ ∀ K, V K → K = J) (hq : Q) =>
        he.elim fun J hj => (hi _ J (selected_union_binary V J hj.1 hj.2)).mpr
          (hs J hj.1 hq))) inv) hv) hu

/-- The exact requirement on a name; equality of its values is intensional. -/
def RepresentsOn {σ : Type} [Ty σ] (A : σ → Prop) (T : σ → Prop → Prop)
    (X : σ → Prop) : Prop :=
  □ (∀ x, X x → A x) ∧ ∀ x, A x → ∀ p, T x p → X x = p

/-- Uniqueness needs rigidity and totality, but not ND or RC. -/
theorem restricted_name_unique {σ : Type} [Ty σ]
    (A : σ → Prop) (T : σ → Prop → Prop) (hA : Rigid A)
    (total : ∀ x, A x → ∃ p, T x p)
    (X Y : σ → Prop) (hx : RepresentsOn A T X) (hy : RepresentsOn A T Y) : X = Y := by
  have hxy : □ (∀ x, A x → X x = Y x) := restricted_barcan_unary A _ hA
    (fun x ha => (total x ha).elim fun p hp =>
      necessity_of_identity _ _ ((hx.2 x ha p hp).trans (hy.2 x ha p hp).symm))
  exact intensionality X Y (modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (h1 : ∀ x, X x → A x) (h2 : ∀ x, Y x → A x)
      (h3 : ∀ x, A x → X x = Y x) (x : σ) =>
        (show X x ↔ Y x from ⟨fun h => (h3 x (h1 x h)) ▸ h,
          fun h => (h3 x (h2 x h)).symm ▸ h⟩))) hx.1) hy.1) hxy)

/-- Partial name representation on a rigid ND domain. Only binary current RC is used. -/
theorem restricted_name_representation {σ : Type} [Ty σ]
    (rc : P.RigidComprehension (σ → Prop → Prop))
    (A : σ → Prop) (T : σ → Prop → Prop) (hA : Rigid A)
    (nd : ∀ x y, A x → A y → x ≠ y → □ (x ≠ y))
    (total : ∀ x, A x → ∃ p, T x p)
    (functional : ∀ x, A x → ∀ p q, T x p → T x q → p = q) :
    ∃ X, RepresentsOn A T X ∧ ∀ Y, RepresentsOn A T Y → Y = X := by
  obtain ⟨R, hR, hco⟩ := rc (fun x p => A x ∧ T x p)
  let X : σ → Prop := fun x => A x ∧ ∃ p, R x p ∧ p
  have hx : RepresentsOn A T X := by
    refine ⟨nec% (fun (x : σ) (h : X x) => h.1), ?_⟩
    intro x ha p hp
    have hr : □ (R x p) := box_elim hR.1 x p ((hco x p).mp ⟨ha, hp⟩)
    have hax : □ (A x) := box_elim hA.1 x ha
    have hf : □ (∀ y q, R y q → y = x → q = p) :=
      restricted_barcan R (fun y q => y = x → q = p) hR.2 (by
        intro y q hyq
        obtain ⟨hay, ht⟩ := (hco y q).mpr hyq
        refine (em (y = x)).elim ?_ ?_
        · intro he
          have heq : q = p := functional x ha q p (he ▸ ht) hp
          exact box_imp_of_box _ _ (necessity_of_identity q p heq)
        · intro hn
          exact box_imp_of_box_not _ _ (nd y x hay ha hn))
    exact modalized_fregean (X x) p (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (hxA : A x) (hxR : R x p)
        (hfun : ∀ y q, R y q → y = x → q = p) =>
          (show X x ↔ p from
            ⟨fun h => h.2.elim fun q hq => (hfun x q hq.1 rfl) ▸ hq.2,
             fun h => ⟨hxA, p, hxR, h⟩⟩))) hax) hr) hf)
  exact ⟨X, hx, fun Y hy => restricted_name_unique A T hA total Y X hy hx⟩

#classicism_check rigid_eq_of_coext rigid_representatives restricted_barcan
  restricted_barcan_unary restricted_barcan_dual CoextensionInvariant selected_union
  local_selection local_selection_binary selected_union_binary RepresentsOn restricted_name_unique restricted_name_representation
#classicism_types rigid_eq_of_coext rigid_representatives restricted_barcan
  restricted_barcan_unary restricted_barcan_dual selected_union
  local_selection local_selection_binary selected_union_binary restricted_name_unique restricted_name_representation
end Classicism.MathematicalContingency
