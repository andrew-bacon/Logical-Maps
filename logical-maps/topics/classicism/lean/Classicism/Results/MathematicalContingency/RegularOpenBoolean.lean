import Classicism.Results.MathematicalContingency.RegularOpenLattice
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α : Type} [Ty α]

def RONeg (Q : α → Prop) (E : α → α → Prop) (U : α → Prop) (q : α) : Prop :=
  Q q ∧ ∀ r, E r q → ¬ U r

theorem roMeet_iff (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (U V W : α → Prop) (hu : ROCarrier Q E U) (hv : ROCarrier Q E V)
    (hw : Meets (ROCarrier Q E) (ROOrder Q E) U V W) : ∀ q, W q ↔ U q ∧ V q := by
  have co := roInfimum_characterization Q E hp rc (fun T => T = U ∨ T = V)
    (fun T h => h.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hv)) W hw
  intro q
  exact ⟨fun h => ⟨((co q).mp h).2 U (Or.inl rfl),((co q).mp h).2 V (Or.inr rfl)⟩,
    fun h => (co q).mpr ⟨((hu.2 q).mp h.1).1,fun T ht =>
      ht.elim (fun e => e.symm ▸ h.1) (fun e => e.symm ▸ h.2)⟩⟩

theorem roJoin_iff (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (U V W : α → Prop) (hu : ROCarrier Q E U) (hv : ROCarrier Q E V)
    (hw : Joins (ROCarrier Q E) (ROOrder Q E) U V W) :
    ∀ q, W q ↔ ROHull Q E (fun r => U r ∨ V r) q := by
  have co := roSupremum_characterization Q E hp rc (fun T => T = U ∨ T = V)
    (fun T h => h.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hv)) W hw
  intro q
  constructor
  · intro h
    apply roHull_mono Q E _ _ _ q ((co q).mp h)
    intro r hr
    obtain ⟨T,ht,htr⟩ := hr
    exact ht.elim (fun e => Or.inl (e ▸ htr)) (fun e => Or.inr (e ▸ htr))
  · intro h
    apply (co q).mpr
    exact roHull_mono Q E _ _ (fun r hr =>
      hr.elim (fun h => ⟨U,Or.inl rfl,h⟩) (fun h => ⟨V,Or.inr rfl,h⟩)) q h

theorem roMeet_of_coext (Q : α → Prop) (E : α → α → Prop)
    (U V W : α → Prop) (hu : ROCarrier Q E U) (hv : ROCarrier Q E V)
    (hw : ROCarrier Q E W) (co : ∀ q, W q ↔ U q ∧ V q) :
    Meets (ROCarrier Q E) (ROOrder Q E) U V W := by
  refine ⟨hw,?_,?_⟩
  · intro T ht
    exact ht.elim (fun e => e.symm ▸ (show ROOrder Q E W U from ⟨hw,hu,fun q h => ((co q).mp h).1⟩))
      (fun e => e.symm ▸ (show ROOrder Q E W V from ⟨hw,hv,fun q h => ((co q).mp h).2⟩))
  · intro T ht bound
    exact ⟨ht,hw,fun q h => (co q).mpr ⟨(bound U (Or.inl rfl)).2.2 q h,(bound V (Or.inr rfl)).2.2 q h⟩⟩

theorem roJoin_of_coext (Q : α → Prop) (E : α → α → Prop)
    (U V W : α → Prop) (hu : ROCarrier Q E U) (hv : ROCarrier Q E V)
    (hw : ROCarrier Q E W) (co : ∀ q, W q ↔ ROHull Q E (fun r => U r ∨ V r) q) :
    Joins (ROCarrier Q E) (ROOrder Q E) U V W := by
  have ubU : ROOrder Q E U W := ⟨hu,hw,fun q h => (co q).mpr
    (roHull_mono Q E U _ (fun _ hx => Or.inl hx) q ((hu.2 q).mp h))⟩
  have ubV : ROOrder Q E V W := ⟨hv,hw,fun q h => (co q).mpr
    (roHull_mono Q E V _ (fun _ hx => Or.inr hx) q ((hv.2 q).mp h))⟩
  refine ⟨hw,fun T ht => ht.elim (fun e => e.symm ▸ ubU) (fun e => e.symm ▸ ubV),?_⟩
  intro T ht bound
  exact ⟨hw,ht,fun q h => (ht.2 q).mpr (roHull_mono Q E _ T
    (fun r hr => hr.elim ((bound U (Or.inl rfl)).2.2 r) ((bound V (Or.inr rfl)).2.2 r)) q ((co q).mp h))⟩

theorem roNeg_fixed (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (U : α → Prop) (down : RODown E U) : ROFixed Q E (RONeg Q E U) := by
  intro q
  constructor
  · apply roHull_extensive Q E hp (RONeg Q E U) (fun _ h => h.1)
    intro p q h hq
    exact ⟨(hp.1 p q h).1,fun r hr => hq.2 r (hp.2.2.2 r p q hr h)⟩
  · intro h
    refine ⟨h.1,?_⟩
    intro r hr hu
    obtain ⟨s,hs,hn⟩ := h.2 r hr
    exact hn.2 s (hp.2.1 s hn.1) (down s r hs hu)

theorem roEndpoints_exist (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    ∃ o i, Endpoints (ROCarrier Q E) (ROOrder Q E) o i ∧
      (∀ q, ¬ o q) ∧ (∀ q, i q ↔ Q q) := by
  have hf : ROFixed Q E (fun _ => True ∧ False) := fun q =>
    ⟨fun h => False.elim h.2,fun h => (h.2 q (hp.2.1 q h.1)).elim (fun _ hs => hs.2)⟩
  have ht : ROFixed Q E Q := fun q => ⟨roHull_extensive Q E hp Q (fun _ h => h)
    (fun p q h _ => (hp.1 p q h).1) q,fun h => h.1⟩
  obtain ⟨o,ho,co⟩ := rc (fun _ => True ∧ False)
  obtain ⟨i,hi,ci⟩ := rc Q
  have bo : ROCarrier Q E o := ⟨ho,roFixed_coext Q E _ o hf co⟩
  have bi : ROCarrier Q E i := ⟨hi,roFixed_coext Q E Q i ht ci⟩
  exact ⟨o,i,⟨bo,bi,fun U hu => ⟨⟨bo,hu,fun q h => False.elim ((co q).mpr h).2⟩,
    ⟨hu,bi,fun q h => (ci q).mp ((hu.2 q).mp h).1⟩⟩⟩,
    fun q h => ((co q).mpr h).2,fun q => (ci q).symm⟩

theorem roComplement_exists (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop))
    (o i U : α → Prop) (he : Endpoints (ROCarrier Q E) (ROOrder Q E) o i)
    (zero : ∀ q, ¬ o q) (top : ∀ q, i q ↔ Q q) (hu : ROCarrier Q E U) :
    ∃ V, ROCarrier Q E V ∧ Meets (ROCarrier Q E) (ROOrder Q E) U V o ∧
      Joins (ROCarrier Q E) (ROOrder Q E) U V i := by
  obtain ⟨V,hr,co⟩ := rc (RONeg Q E U)
  have hv : ROCarrier Q E V := ⟨hr,roFixed_coext Q E _ V
    (roNeg_fixed Q E hp U (roFixed_down Q E hp U hu.2)) co⟩
  refine ⟨V,hv,roMeet_of_coext Q E U V o hu hv he.1 ?_,roJoin_of_coext Q E U V i hu hv he.2.1 ?_⟩
  · intro q
    exact ⟨fun h => False.elim (zero q h),fun h => False.elim
      (((co q).mpr h.2).2 q (hp.2.1 q ((hu.2 q).mp h.1).1) h.1)⟩
  · intro q
    constructor
    · intro h
      refine ⟨(top q).mp h,?_⟩
      intro r hrq
      obtain yes | no := em (∃ s, E s r ∧ U s)
      · exact yes.elim (fun s hs => ⟨s,hs.1,Or.inl hs.2⟩)
      · have hn : RONeg Q E U r := ⟨(hp.1 r q hrq).1,fun s hs hu => no ⟨s,hs,hu⟩⟩
        exact ⟨r,hp.2.1 r hn.1,Or.inr ((co r).mp hn)⟩
    · exact fun h => (top q).mpr h.1

theorem roDistributive (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    DistributiveOn (ROCarrier Q E) (ROOrder Q E) := by
  intro X Y Z J L R S hx hy hz hj hl hr hs
  have cj := roJoin_iff Q E hp rc Y Z J hy hz hj
  have cl := roMeet_iff Q E hp rc X J L hx hj.1 hl
  have cr := roMeet_iff Q E hp rc X Y R hx hy hr
  have cs := roMeet_iff Q E hp rc X Z S hx hz hs
  have rl : ROOrder Q E R L := ⟨hr.1,hl.1,fun q h => (cl q).mpr
    ⟨((cr q).mp h).1,(hj.2.1 Y (Or.inl rfl)).2.2 q ((cr q).mp h).2⟩⟩
  have sl : ROOrder Q E S L := ⟨hs.1,hl.1,fun q h => (cl q).mpr
    ⟨((cs q).mp h).1,(hj.2.1 Z (Or.inr rfl)).2.2 q ((cs q).mp h).2⟩⟩
  refine ⟨hl.1,fun T ht => ht.elim (fun e => e.symm ▸ rl) (fun e => e.symm ▸ sl),?_⟩
  intro W hw bound
  refine ⟨hl.1,hw,?_⟩
  intro q hq
  obtain ⟨xq,jq⟩ := (cl q).mp hq
  apply (hw.2 q).mpr
  refine ⟨((hx.2 q).mp xq).1,?_⟩
  intro r hrq
  obtain ⟨s,hsr,ys⟩ := ((cj q).mp jq).2 r hrq
  have xs := roFixed_down Q E hp X hx.2 s q (hp.2.2.2 s r q hsr hrq) xq
  exact ⟨s,hsr,ys.elim (fun h => (bound R (Or.inl rfl)).2.2 s ((cr s).mpr ⟨xs,h⟩))
    (fun h => (bound S (Or.inr rfl)).2.2 s ((cs s).mpr ⟨xs,h⟩))⟩

theorem regularOpen_cba (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    CBA (ROCarrier Q E) (ROOrder Q E) := by
  obtain ⟨o,i,he,hzero,htop⟩ := roEndpoints_exist Q E hp rc
  exact ⟨roOrder_partialOrder Q E,
    fun X hs => (roSupremum_exists Q E hp rc X hs).elim (fun V hv => ⟨V,hv.1⟩),
    fun X hs => (roInfimum_exists Q E hp rc X hs).elim (fun V hv => ⟨V,hv.1⟩),
    roDistributive Q E hp rc,o,i,he,fun U hu => roComplement_exists Q E hp rc o i U he hzero htop hu⟩

#classicism_check roMeet_iff roJoin_iff roMeet_of_coext roJoin_of_coext roNeg_fixed roEndpoints_exist roComplement_exists roDistributive regularOpen_cba
#classicism_types roMeet_iff roJoin_iff roMeet_of_coext roJoin_of_coext roNeg_fixed roEndpoints_exist roComplement_exists roDistributive regularOpen_cba
end Classicism.MathematicalContingency
