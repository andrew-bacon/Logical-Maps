import Classicism.Results.MathematicalContingency.RegularOpenHull
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α : Type} [Ty α]

def ROUnion (X : (α → Prop) → Prop) (q : α) : Prop := ∃ U, X U ∧ U q
def ROIntersection (Q : α → Prop) (X : (α → Prop) → Prop) (q : α) : Prop :=
  Q q ∧ ∀ U, X U → U q

theorem roIntersection_fixed (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (X : (α → Prop) → Prop)
    (sub : ∀ U, X U → ROCarrier Q E U) : ROFixed Q E (ROIntersection Q X) := by
  intro q
  constructor
  · apply roHull_extensive Q E hp (ROIntersection Q X) (fun _ h => h.1)
    intro p q h hq
    exact ⟨(hp.1 p q h).1,fun U hu => roFixed_down Q E hp U (sub U hu).2 p q h (hq.2 U hu)⟩
  · intro h
    exact ⟨h.1,fun U hu => ((sub U hu).2 q).mpr
      (roHull_mono Q E (ROIntersection Q X) U (fun _ hx => hx.2 U hu) q h)⟩

theorem roSupremum_exists (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (X : (α → Prop) → Prop) (sub : ∀ U, X U → ROCarrier Q E U) :
    ∃ V, Supremum (ROCarrier Q E) (ROOrder Q E) X V ∧
      ∀ q, V q ↔ ROHull Q E (ROUnion X) q := by
  obtain ⟨V,hv,co⟩ := roHull_representative Q E hp rc (ROUnion X)
  refine ⟨V,⟨hv,?_,?_⟩,co⟩
  · intro U hu
    exact ⟨sub U hu,hv,fun q hq => (co q).mpr
      (roHull_mono Q E U (ROUnion X) (fun r hr => ⟨U,hu,hr⟩) q (((sub U hu).2 q).mp hq))⟩
  · intro W hw bound
    exact ⟨hv,hw,fun q hq => (hw.2 q).mpr
      (roHull_mono Q E (ROUnion X) W
        (fun r hr => hr.elim (fun U hu => (bound U hu.1).2.2 r hu.2)) q ((co q).mp hq))⟩

theorem roInfimum_exists (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (X : (α → Prop) → Prop) (sub : ∀ U, X U → ROCarrier Q E U) :
    ∃ V, Infimum (ROCarrier Q E) (ROOrder Q E) X V ∧
      ∀ q, V q ↔ ROIntersection Q X q := by
  obtain ⟨V,hr,co⟩ := rc (ROIntersection Q X)
  have hv : ROCarrier Q E V := ⟨hr,roFixed_coext Q E (ROIntersection Q X) V
    (roIntersection_fixed Q E hp X sub) co⟩
  refine ⟨V,⟨hv,?_,?_⟩,fun q => (co q).symm⟩
  · intro U hu
    exact ⟨hv,sub U hu,fun q hq => ((co q).mpr hq).2 U hu⟩
  · intro W hw bound
    exact ⟨hw,hv,fun q hq => (co q).mp ⟨((hw.2 q).mp hq).1,
      fun U hu => (bound U hu).2.2 q hq⟩⟩

theorem roSupremum_characterization (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (X : (α → Prop) → Prop) (sub : ∀ U, X U → ROCarrier Q E U)
    (V : α → Prop) (hv : Supremum (ROCarrier Q E) (ROOrder Q E) X V) :
    ∀ q, V q ↔ ROHull Q E (ROUnion X) q := by
  obtain ⟨W,hw,co⟩ := roSupremum_exists Q E hp rc X sub
  intro q
  exact ⟨fun h => (co q).mp ((hv.2.2 W hw.1 hw.2.1).2.2 q h),
    fun h => (hw.2.2 V hv.1 hv.2.1).2.2 q ((co q).mpr h)⟩

theorem roInfimum_characterization (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (X : (α → Prop) → Prop) (sub : ∀ U, X U → ROCarrier Q E U)
    (V : α → Prop) (hv : Infimum (ROCarrier Q E) (ROOrder Q E) X V) :
    ∀ q, V q ↔ ROIntersection Q X q := by
  obtain ⟨W,hw,co⟩ := roInfimum_exists Q E hp rc X sub
  intro q
  exact ⟨fun h => (co q).mp ((hw.2.2 V hv.1 hv.2.1).2.2 q h),
    fun h => (hv.2.2 W hw.1 hw.2.1).2.2 q ((co q).mpr h)⟩

#classicism_check roIntersection_fixed roSupremum_exists roInfimum_exists roSupremum_characterization roInfimum_characterization
#classicism_types roIntersection_fixed roSupremum_exists roInfimum_exists roSupremum_characterization roInfimum_characterization
end Classicism.MathematicalContingency
