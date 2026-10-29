import Classicism.Results.MathematicalContingency.NaturalRecursion
import Classicism.Results.MathematicalContingency.FiniteSubsetOrder
import Classicism.Results.MathematicalContingency.NaturalWellOrder
import Classicism.Results.MathematicalContingency.SerialCounting

/-! Canonical finite ranks as first visits of the increasing relational enumeration. -/
namespace Classicism.MathematicalContingency
variable {σ α : Type} [Ty σ] [Ty α]

def MinimumOn (X : α → Prop) (L : α → α → Prop) (z : α) : Prop :=
  X z ∧ ∀ y, X y → ¬ L y z

def NextIn (X : α → Prop) (L : α → α → Prop) (a b : α) : Prop :=
  X a ∧ ((X b ∧ L a b ∧ ∀ c, X c → L a c → ¬ L c b) ∨
    (b = a ∧ ∀ c, X c → ¬ L a c))

def RankRun (X : α → Prop) (L : α → α → Prop) (n : (σ → Prop) → Prop) (a : α) : Prop :=
  ∃ z, MinimumOn X L z ∧ NatRun (fun _ => NextIn X L) z n a

def FiniteRank (X : α → Prop) (L : α → α → Prop) (a : α) (n : (σ → Prop) → Prop) : Prop :=
  LeastRelated X LowerNat LowerLT (fun a n => RankRun X L n a) a n

theorem minimumOn_exists (A X : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (sub : ∀ x, X x → A x) (he : ∃ x, X x) : ∃ z, MinimumOn X L z :=
  hw.2 X sub he

theorem minimumOn_unique (A X : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (sub : ∀ x, X x → A x)
    (a b : α) (ha : MinimumOn X L a) (hb : MinimumOn X L b) : a = b := by
  obtain e | h | h := hl.2.2.2 a b (sub a ha.1) (sub b hb.1)
  · exact e
  · exact (hb.2 a ha.1 h).elim
  · exact (ha.2 b hb.1 h).elim

theorem nextIn_member (X : α → Prop) (L : α → α → Prop) (a b : α) (h : NextIn X L a b) : X b :=
  h.2.elim (fun k => k.1) (fun k => k.1.symm ▸ h.1)

theorem nextIn_total (A X : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (sub : ∀ x, X x → A x) (a : α) (ha : X a) : ∃ b, NextIn X L a b := by
  obtain he | hn := em (∃ b, X b ∧ L a b)
  · obtain ⟨b,hb,hm⟩ := hw.2 (fun b => X b ∧ L a b) (fun b h => sub b h.1) he
    exact ⟨b,ha,Or.inl ⟨hb.1,hb.2,fun c hc hL => hm c ⟨hc,hL⟩⟩⟩
  · exact ⟨a,ha,Or.inr ⟨rfl,fun c hc hL => hn ⟨c,hc,hL⟩⟩⟩

theorem nextIn_functional (A X : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (sub : ∀ x, X x → A x)
    (a b c : α) (hb : NextIn X L a b) (hc : NextIn X L a c) : b = c := by
  obtain hb' | hb' := hb.2
  · obtain hc' | hc' := hc.2
    · obtain e | h | h := hl.2.2.2 b c (sub b hb'.1) (sub c hc'.1)
      · exact e
      · exact (hc'.2.2 b hb'.1 hb'.2.1 h).elim
      · exact (hb'.2.2 c hc'.1 hc'.2.1 h).elim
    · exact (hc'.2 b hb'.1 hb'.2.1).elim
  · obtain hc' | hc' := hc.2
    · exact (hb'.2 c hc'.1 hc'.2.1).elim
    · exact hb'.1.trans hc'.1.symm

theorem nextIn_below_candidate (A X : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (sub : ∀ x, X x → A x)
    (a b c : α) (hn : NextIn X L a b) (hc : X c) (hac : L a c) :
    L a b ∧ (b = c ∨ L b c) := by
  obtain h | h := hn.2
  · refine ⟨h.2.1,?_⟩
    obtain e | hbc | hcb := hl.2.2.2 b c (sub b h.1) (sub c hc)
    · exact Or.inl e
    · exact Or.inr hbc
    · exact (h.2.2 c hc hac hcb).elim
  · exact (h.2 c hc hac).elim

theorem rankRun_data (X : α → Prop) (L : α → α → Prop)
    (n : (σ → Prop) → Prop) (a : α) (h : RankRun X L n a) : LowerNat n ∧ X a := by
  obtain ⟨z,hz,hr⟩ := h
  exact natRun_data X (fun _ => NextIn X L) z hz.1
    (fun _ a b _ _ ht => nextIn_member X L a b ht) n a hr

theorem rankRun_functional (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (sub : ∀ x, X x → A x)
    (n : (σ → Prop) → Prop) (a b : α) (ha : RankRun X L n a) (hb : RankRun X L n b) : a = b := by
  have hn := (rankRun_data X L n a ha).1
  obtain ⟨z,hz,hza⟩ := ha
  obtain ⟨w,hw,hwb⟩ := hb
  have e := minimumOn_unique A X L hl sub z w hz hw
  have hzb : NatRun (fun _ => NextIn X L) z n b := e.symm ▸ hwb
  exact natRun_functional hp (fun _ => NextIn X L) z
    (fun _ a b c _ hb hc => nextIn_functional A X L hl sub a b c hb hc) n hn a b hza hzb

/-- A finite ordered subset cannot have an unvisited element above all visited predecessors. -/
theorem rankRun_surjective (A X : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (hf : FiniteSubset A X) (a : α) (ha : X a) :
    ∃ n : (σ → Prop) → Prop, LowerNat n ∧ RankRun X L n a := by
  have sub := finiteSubset_members A X hf
  obtain ⟨z,hz⟩ := minimumOn_exists A X L hw sub ⟨a,ha⟩
  have hza : z = a ∨ L z a := by
    obtain e | h | h := hw.1.2.2.2 z a (sub z hz.1) (sub a ha)
    · exact Or.inl e
    · exact Or.inr h
    · exact (hz.2 a ha h).elim
  let V := fun x => X x ∧ (x = a ∨ L x a) ∧
    ∃ n : (σ → Prop) → Prop, LowerNat n ∧ NatRun (fun _ => NextIn X L) z n x
  have hV : FiniteSubset A V := finiteSubset_subset A X V hf (fun x h => h.1)
  have hvz : V z := ⟨hz.1,hza,AtLeastZero σ,lowerNat_zero,natRun_zero _ z⟩
  obtain ⟨b,hb,hmax⟩ := finiteSubset_greatest A L hw.1 V hV ⟨z,hvz⟩
  obtain ⟨n,hn,hr⟩ := hb.2.2
  obtain e | hba := hb.2.1
  · exact ⟨n,hn,z,hz,e ▸ hr⟩
  · obtain ⟨c,hc⟩ := nextIn_total A X L hw sub b hb.1
    obtain ⟨hbc,hca⟩ := nextIn_below_candidate A X L hw.1 sub b c a hc ha hba
    have hrun := natRun_step (fun _ => NextIn X L) z b c n hn hr hc
    have hVc : V c := ⟨nextIn_member X L b c hc,hca,SucCard n,lowerNat_suc n hn,hrun⟩
    obtain e | hcb := hmax c hVc
    · exact (hw.1.2.1 b (sub b hb.1) (e ▸ hbc)).elim
    · exact (hw.1.2.1 b (sub b hb.1)
        (hw.1.2.2.1 b c b (sub b hb.1) (sub c hVc.1) (sub b hb.1) hbc hcb)).elim

theorem finiteRank_total (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (hf : FiniteSubset A X) (a : α) (ha : X a) :
    ∃ n : (σ → Prop) → Prop, FiniteRank X L a n :=
  leastRelated_exists X LowerNat LowerLT (fun a n => RankRun X L n a) (lowerNat_wellOrder hp)
    (fun a ha => rankRun_surjective A X L hw hf a ha) a ha

theorem finiteRank_functional (hp : LowerPeano σ) (X : α → Prop) (L : α → α → Prop)
    (a : α) (n m : (σ → Prop) → Prop) (hn : FiniteRank X L a n) (hm : FiniteRank X L a m) : n = m :=
  leastRelated_unique X LowerNat LowerLT (fun a n => RankRun X L n a) (lowerNat_wellOrder hp) a n m hn hm

theorem finiteRank_injective (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (sub : ∀ x, X x → A x)
    (a b : α) (n : (σ → Prop) → Prop) (ha : FiniteRank X L a n) (hb : FiniteRank X L b n) : a = b :=
  rankRun_functional hp A X L hl sub n a b ha.2.2.1 hb.2.2.1

theorem finiteRank_injects (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (hf : FiniteSubset A X) : Injects (FiniteRank X L) X (@LowerNat σ _) :=
  ⟨⟨fun a n h => ⟨h.1,h.2.1⟩,
    fun a ha => (finiteRank_total hp A X L hw hf a ha).elim (fun n hn => ⟨n,hn.2.1,hn⟩),
    fun a n m hn hm => finiteRank_functional hp X L a n m hn hm⟩,
    fun a b n ha hb => finiteRank_injective hp A X L hw.1 (finiteSubset_members A X hf) a b n ha hb⟩

#classicism_check minimumOn_exists minimumOn_unique nextIn_member nextIn_total nextIn_functional nextIn_below_candidate rankRun_data rankRun_functional rankRun_surjective finiteRank_total finiteRank_functional finiteRank_injective finiteRank_injects
#classicism_types minimumOn_exists minimumOn_unique nextIn_member nextIn_total nextIn_functional nextIn_below_candidate rankRun_data rankRun_functional rankRun_surjective finiteRank_total finiteRank_functional finiteRank_injective finiteRank_injects
end Classicism.MathematicalContingency
