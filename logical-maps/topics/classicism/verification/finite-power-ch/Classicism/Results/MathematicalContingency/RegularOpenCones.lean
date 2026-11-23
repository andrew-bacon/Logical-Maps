import Classicism.Results.MathematicalContingency.RegularOpenBoolean
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α : Type} [Ty α]

def ROCone (Q : α → Prop) (E : α → α → Prop) (q : α) (U : α → Prop) : Prop :=
  Q q ∧ ROCarrier Q E U ∧ ∀ r, U r ↔ ROHull Q E (fun s => E s q) r

theorem roCone_maps (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    Maps (ROCone Q E) Q (ROCarrier Q E) := by
  refine ⟨fun _ _ h => ⟨h.1,h.2.1⟩,?_,?_⟩
  · intro q hq
    obtain ⟨U,hu,co⟩ := roHull_representative Q E hp rc (fun s => E s q)
    exact ⟨U,hu,hq,hu,co⟩
  · intro q U V hu hv
    exact rigid_eq_of_coext U V hu.2.1.1 hv.2.1.1
      (fun r => (hu.2.2 r).trans (hv.2.2 r).symm)

theorem roCone_contains (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (q p : α) (U : α → Prop)
    (cone : ROCone Q E q U) (h : E p q) : U p := by
  apply (cone.2.2 p).mpr
  exact ⟨(hp.1 p q h).1,fun r hr =>
    ⟨r,hp.2.1 r (hp.1 r p hr).1,hp.2.2.2 r p q hr h⟩⟩

theorem roCone_below (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (q : α) (U V : α → Prop)
    (cone : ROCone Q E q U) (hv : ROCarrier Q E V) (hq : V q) : ROOrder Q E U V := by
  exact ⟨cone.2.1,hv,fun p hu => (hv.2 p).mpr
    (roHull_mono Q E (fun s => E s q) V
      (fun s hs => roFixed_down Q E hp V hv.2 s q hs hq) p ((cone.2.2 p).mp hu))⟩

theorem roEndpoints_extents (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (o i : α → Prop) (he : Endpoints (ROCarrier Q E) (ROOrder Q E) o i) :
    (∀ q, ¬ o q) ∧ (∀ q, i q ↔ Q q) := by
  obtain ⟨z,t,hzt,hz,ht⟩ := roEndpoints_exist Q E hp rc
  exact ⟨fun q h => hz q ((he.2.2 z hzt.1).1.2.2 q h),fun q =>
    ⟨fun h => ((he.2.1.2 q).mp h).1,
      fun h => (he.2.2 t hzt.2.1).2.2.2 q ((ht q).mpr h)⟩⟩

theorem roNonzero_member (Q : α → Prop) (E : α → α → Prop)
    (o U : α → Prop) (ho : ROCarrier Q E o) (zero : ∀ q, ¬ o q)
    (hu : ROCarrier Q E U) (ne : U ≠ o) : ∃ q, U q := by
  obtain h | h := em (∃ q, U q)
  · exact h
  · exact False.elim (ne (rigid_eq_of_coext U o hu.1 ho.1
      (fun q => ⟨fun hq => False.elim (h ⟨q,hq⟩),fun hq => False.elim (zero q hq)⟩)))

theorem regularOpen_denseCones (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (o i : α → Prop) (he : Endpoints (ROCarrier Q E) (ROOrder Q E) o i) :
    DenseCones Q E (ROCarrier Q E) (ROOrder Q E) o (ROCone Q E) := by
  have maps := roCone_maps Q E hp rc
  have zero := (roEndpoints_extents Q E hp rc o i he).1
  refine ⟨maps,?_,?_,?_,?_⟩
  · intro q U hc eq
    have hu := roCone_contains Q E hp q q U hc (hp.2.1 q hc.1)
    exact zero q (eq ▸ hu)
  · intro q r U V hq hr erq
    exact ⟨hr.2.1,hq.2.1,fun p hv => (hq.2.2 p).mpr
      (roHull_mono Q E (fun s => E s r) (fun s => E s q)
        (fun s hs => hp.2.2.2 s r q hs erq) p ((hr.2.2 p).mp hv))⟩
  · intro U hu ne
    obtain ⟨q,hq⟩ := roNonzero_member Q E o U he.1 zero hu ne
    have qq := ((hu.2 q).mp hq).1
    obtain ⟨V,hv,hc⟩ := maps.2.1 q qq
    exact ⟨q,V,qq,hc,roCone_below Q E hp q V U hc hu hq⟩
  · intro q U V hc hv ne vu
    obtain ⟨p,hpV⟩ := roNonzero_member Q E o V he.1 zero hv ne
    have hpU := vu.2.2 p hpV
    have hpQ := ((hv.2 p).mp hpV).1
    obtain ⟨r,hrp,hrq⟩ := ((hc.2.2 p).mp hpU).2 p (hp.2.1 p hpQ)
    have rq := (hp.1 r q hrq).1
    obtain ⟨W,hw,hcone⟩ := maps.2.1 r rq
    exact ⟨r,W,rq,hrq,hcone,roCone_below Q E hp r W V hcone hv
      (roFixed_down Q E hp V hv.2 r p hrp hpV)⟩

theorem regularOpen_incompatibleCones (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (o i : α → Prop) (he : Endpoints (ROCarrier Q E) (ROOrder Q E) o i) :
    IncompatibleCones Q E (ROCarrier Q E) (ROOrder Q E) o (ROCone Q E) := by
  have zero := (roEndpoints_extents Q E hp rc o i he).1
  intro d e U V hd heC incompatible
  apply roMeet_of_coext Q E U V o hd.2.1 heC.2.1 he.1
  intro q
  constructor
  · intro h
    exact False.elim (zero q h)
  · intro h
    have hq := ((hd.2.1.2 q).mp h.1).1
    obtain ⟨r,hrq,hrd⟩ := ((hd.2.2 q).mp h.1).2 q (hp.2.1 q hq)
    have rv := roFixed_down Q E hp V heC.2.1.2 r q hrq h.2
    have rq := (hp.1 r q hrq).1
    obtain ⟨s,hsr,hse⟩ := ((heC.2.2 r).mp rv).2 r (hp.2.1 r rq)
    exact False.elim (incompatible ⟨s,(hp.1 s e hse).1,hp.2.2.2 s r d hsr hrd,hse⟩)

theorem regularOpen_completion (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    CBA (ROCarrier Q E) (ROOrder Q E) ∧
      ∀ o i, Endpoints (ROCarrier Q E) (ROOrder Q E) o i →
        DenseCones Q E (ROCarrier Q E) (ROOrder Q E) o (ROCone Q E) ∧
        IncompatibleCones Q E (ROCarrier Q E) (ROOrder Q E) o (ROCone Q E) :=
  ⟨regularOpen_cba Q E hp rc,fun o i he =>
    ⟨regularOpen_denseCones Q E hp rc o i he,regularOpen_incompatibleCones Q E hp rc o i he⟩⟩

#classicism_check roCone_maps roCone_contains roCone_below roEndpoints_extents roNonzero_member regularOpen_denseCones regularOpen_incompatibleCones regularOpen_completion
#classicism_types roCone_maps roCone_contains roCone_below roEndpoints_extents roNonzero_member regularOpen_denseCones regularOpen_incompatibleCones regularOpen_completion
end Classicism.MathematicalContingency
