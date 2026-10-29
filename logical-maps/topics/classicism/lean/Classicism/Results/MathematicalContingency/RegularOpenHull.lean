import Classicism.Results.MathematicalContingency.ConeSuprema
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α : Type} [Ty α]

/-- Conditions below q meet U densely. Smaller conditions are stronger. -/
def ROHull (Q : α → Prop) (E : α → α → Prop) (U : α → Prop) (q : α) : Prop :=
  Q q ∧ ∀ r, E r q → ∃ s, E s r ∧ U s

def RODown (E : α → α → Prop) (U : α → Prop) : Prop :=
  ∀ p q, E p q → U q → U p

def ROFixed (Q : α → Prop) (E : α → α → Prop) (U : α → Prop) : Prop :=
  ∀ q, U q ↔ ROHull Q E U q

def ROCarrier (Q : α → Prop) (E : α → α → Prop) (U : α → Prop) : Prop :=
  Rigid U ∧ ROFixed Q E U

def ROOrder (Q : α → Prop) (E : α → α → Prop) (U V : α → Prop) : Prop :=
  ROCarrier Q E U ∧ ROCarrier Q E V ∧ ∀ q, U q → V q

theorem roHull_mono (Q : α → Prop) (E : α → α → Prop) (U V : α → Prop)
    (h : ∀ q, U q → V q) : ∀ q, ROHull Q E U q → ROHull Q E V q := by
  intro q hq
  exact ⟨hq.1,fun r hr => (hq.2 r hr).elim (fun s hs => ⟨s,hs.1,h s hs.2⟩)⟩

theorem roHull_down (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (U : α → Prop) : RODown E (ROHull Q E U) := by
  intro p q h hq
  exact ⟨(hp.1 p q h).1,fun r hr => hq.2 r (hp.2.2.2 r p q hr h)⟩

theorem roHull_extensive (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (U : α → Prop)
    (sub : ∀ q, U q → Q q) (down : RODown E U) : ∀ q, U q → ROHull Q E U q := by
  intro q hq
  exact ⟨sub q hq,fun r hr => ⟨r,hp.2.1 r (hp.1 r q hr).1,down r q hr hq⟩⟩

theorem roHull_idempotent (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (U : α → Prop) : ROFixed Q E (ROHull Q E U) := by
  intro q
  constructor
  · exact roHull_extensive Q E hp (ROHull Q E U) (fun _ h => h.1) (roHull_down Q E hp U) q
  · intro h
    refine ⟨h.1,?_⟩
    intro r hr
    obtain ⟨s,hs,hu⟩ := h.2 r hr
    obtain ⟨t,ht,hut⟩ := hu.2 s (hp.2.1 s hu.1)
    exact ⟨t,hp.2.2.2 t s r ht hs,hut⟩

theorem roFixed_coext (Q : α → Prop) (E : α → α → Prop) (U V : α → Prop)
    (hu : ROFixed Q E U) (co : ∀ q, U q ↔ V q) : ROFixed Q E V := by
  intro q
  exact ⟨fun h => roHull_mono Q E U V (fun x hx => (co x).mp hx) q ((hu q).mp ((co q).mpr h)),
    fun h => (co q).mp ((hu q).mpr (roHull_mono Q E V U (fun x hx => (co x).mpr hx) q h))⟩

theorem roFixed_down (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (U : α → Prop) (hu : ROFixed Q E U) : RODown E U := by
  intro p q h hq
  exact (hu p).mpr (roHull_down Q E hp U p q h ((hu q).mp hq))

theorem roHull_representative (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) (U : α → Prop) :
    ∃ V, ROCarrier Q E V ∧ ∀ q, V q ↔ ROHull Q E U q := by
  obtain ⟨V,hv,co⟩ := rc (ROHull Q E U)
  exact ⟨V,⟨hv,roFixed_coext Q E (ROHull Q E U) V (roHull_idempotent Q E hp U) co⟩,
    fun q => (co q).symm⟩

theorem roOrder_partialOrder (Q : α → Prop) (E : α → α → Prop) :
    PartialOrderOn (ROCarrier Q E) (ROOrder Q E) := by
  refine ⟨fun _ _ h => ⟨h.1,h.2.1⟩,fun _ h => ⟨h,h,fun _ hu => hu⟩,?_,?_⟩
  · intro U V h k
    exact rigid_eq_of_coext U V h.1.1 h.2.1.1 (fun q => ⟨h.2.2 q,k.2.2 q⟩)
  · intro U V W h k
    exact ⟨h.1,k.2.1,fun q hu => k.2.2 q (h.2.2 q hu)⟩

#classicism_check roHull_mono roHull_down roHull_extensive roHull_idempotent roFixed_coext roFixed_down roHull_representative roOrder_partialOrder
#classicism_types roHull_mono roHull_down roHull_extensive roHull_idempotent roFixed_coext roFixed_down roHull_representative roOrder_partialOrder
end Classicism.MathematicalContingency
