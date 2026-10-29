import Classicism.Results.MathematicalContingency.ConeAntichains
import Classicism.Results.MathematicalContingency.SerialCounting
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

/-- Pull a nonzero proposition back through the current relational representation. -/
def FibrePullback (A : α → Prop) (D : α → β → Prop) (F : γ → Prop → Prop)
    (y : β) (x : α) (b : γ) : Prop := A x ∧ D x y ≠ False ∧ F b (D x y)

def FibreAntichain (A : α → Prop) (D : α → β → Prop) (F : γ → Prop → Prop)
    (y : β) (b : γ) : Prop := ∃ x, FibrePullback A D F y x b

theorem disjoint_equal_zero (p q : Prop) (hd : □ (¬ (p ∧ q))) (he : p = q) : p = False := by
  have hd' : □ (¬ (p ∧ p)) := he.symm ▸ hd
  exact (box_not_eq p).mp (modal_K _ _ (nec% (fun (h : ¬ (p ∧ p)) (hp : p) => h ⟨hp,hp⟩)) hd')

theorem disjoint_lower_zero (p q s : Prop) (hd : □ (¬ (p ∧ q)))
    (hsp : EntailmentOrder s p) (hsq : EntailmentOrder s q) : s = False :=
  (box_not_eq s).mp (modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (h : ¬ (p ∧ q)) (hp : s → p) (hq : s → q) (hs : s) => h ⟨hp hs,hq hs⟩)) hd) hsp) hsq)

theorem fibrePullback_maps (A : α → Prop) (D : α → β → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (y : β)
    (below : ∀ x, A x → Below P (D x y)) :
    Maps (FibrePullback A D F y) (fun x => A x ∧ D x y ≠ False) (FibreAntichain A D F y) := by
  refine ⟨fun x b h => ⟨⟨h.1,h.2.1⟩,x,h⟩,?_,?_⟩
  · intro x hx
    obtain ⟨b,_,hb⟩ := hf.1.2.2 (D x y) (below x hx.1)
    exact ⟨b,⟨x,hx.1,hx.2,hb⟩,hx.1,hx.2,hb⟩
  · intro x b c hb hc
    exact hf.1.1.2 b c (D x y) hb.2.2 hc.2.2

theorem fibrePullback_injects (A : α → Prop) (D : α → β → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (y : β)
    (below : ∀ x, A x → Below P (D x y))
    (disjoint : ∀ x z, A x → A z → x ≠ z → □ (¬ (D x y ∧ D z y))) :
    Injects (FibrePullback A D F y) (fun x => A x ∧ D x y ≠ False) (FibreAntichain A D F y) := by
  refine ⟨fibrePullback_maps A D H R F P hf y below,?_⟩
  intro x z b hx hz
  apply (em (x = z)).elim id
  intro hn
  exact (hx.2.1 (disjoint_equal_zero (D x y) (D z y) (disjoint x z hx.1 hz.1 hn)
    (hf.1.1.1.2.2 b (D x y) (D z y) hx.2.2 hz.2.2))).elim

theorem fibreAntichain_nonzero (A : α → Prop) (D : α → β → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (F : γ → Prop → Prop) (P : Prop) (o : γ)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False) (y : β)
    (disjoint : ∀ x z, A x → A z → x ≠ z → □ (¬ (D x y ∧ D z y))) :
    NonzeroAntichain H R o (FibreAntichain A D F y) := by
  constructor
  · intro b hb
    obtain ⟨x,hx⟩ := hb
    exact ⟨(hf.1.1.1.1 b (D x y) hx.2.2).1,
      fun e => hx.2.1 ((intervalIso_zero_iff H R F P hf o b (D x y) ho hx.2.2).mp e)⟩
  · intro b c v hb hc hne hv hvb hvc
    obtain ⟨x,hx⟩ := hb
    obtain ⟨z,hz⟩ := hc
    have hn : x ≠ z := by
      intro e
      have hz' : F c (D x y) := e.symm ▸ hz.2.2
      exact hne (hf.1.1.2 b c (D x y) hx.2.2 hz')
    obtain ⟨s,_,hvs⟩ := hf.1.1.1.2.1 v hv
    apply (intervalIso_zero_iff H R F P hf o v s ho hvs).mpr
    exact disjoint_lower_zero (D x y) (D z y) s (disjoint x z hx.1 hz.1 hn)
      (intervalIso_order_forward H R F P hf v b s (D x y) hvs hx.2.2 hvb)
      (intervalIso_order_forward H R F P hf v c s (D z y) hvs hz.2.2 hvc)

/-- Uniform bounds on Boolean antichains yield uniform codes for proposition fibres. -/
theorem antichain_uniform_fibre_codes (A : α → Prop) (B : β → Prop) (K : δ → Prop)
    (D : α → β → Prop) (H : γ → Prop) (R : γ → γ → Prop)
    (F : γ → Prop → Prop) (P : Prop) (o : γ)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (below : ∀ x y, A x → B y → Below P (D x y))
    (disjoint : ∀ x z y, A x → A z → B y → x ≠ z → □ (¬ (D x y ∧ D z y)))
    (count : ∀ V : β → γ → Prop, (∀ y, B y → NonzeroAntichain H R o (V y)) →
      ∃ T : β → γ → δ → Prop, ∀ y, B y → Injects (T y) (V y) K) :
    ∃ S, UniformFibreCodes A B K (fun x y => D x y ≠ False) S := by
  obtain ⟨T,hT⟩ := count (FibreAntichain A D F)
    (fun y hy => fibreAntichain_nonzero A D H R F P o hf ho y (fun x z hx hz hn => disjoint x z y hx hz hy hn))
  exact ⟨fun y => RelCompose (FibrePullback A D F y) (T y),fun y hy =>
    injects_compose _ _ (fun x => A x ∧ D x y ≠ False) (FibreAntichain A D F y) K
      (fibrePullback_injects A D H R F P hf y (fun x hx => below x y hx hy)
        (fun x z hx hz hn => disjoint x z y hx hz hy hn)) (hT y hy)⟩

theorem antichain_serial_embeds_product (A : α → Prop) (B : β → Prop) (K : δ → Prop)
    (L : β → β → Prop) (D : α → β → Prop) (H : γ → Prop) (R : γ → γ → Prop)
    (F : γ → Prop → Prop) (P : Prop) (o : γ)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (below : ∀ x y, A x → B y → Below P (D x y))
    (disjoint : ∀ x z y, A x → A z → B y → x ≠ z → □ (¬ (D x y ∧ D z y)))
    (count : ∀ V : β → γ → Prop, (∀ y, B y → NonzeroAntichain H R o (V y)) →
      ∃ T : β → γ → δ → Prop, ∀ y, B y → Injects (T y) (V y) K)
    (hw : WellOrderOn B L) (serial : ∀ x, A x → ∃ y, B y ∧ D x y ≠ False)
    (rc : Classicism.P.RigidComprehension (β → δ → Prop)) : Embeds A (RelProduct B K) := by
  obtain ⟨S,hS⟩ := antichain_uniform_fibre_codes A B K D H R F P o hf ho below disjoint count
  exact serial_embeds_product A B K L (fun x y => D x y ≠ False) S hw serial hS rc

/-- Restricted Barcan turns possible coverage into current seriality. -/
theorem rigid_nonzero_serial (A : α → Prop) (B : β → Prop) (D : α → β → Prop) (Q : Prop)
    (hb : Rigid B) (hq : Q ≠ False)
    (cover : ∀ x, A x → EntailmentOrder Q (∃ y, B y ∧ D x y)) :
    ∀ x, A x → ∃ y, B y ∧ D x y ≠ False := by
  intro x hx
  exact restricted_barcan_dual B (D x) hb
    (dia_mono Q (∃ y, B y ∧ D x y) (cover x hx) hq)

#classicism_check disjoint_equal_zero disjoint_lower_zero fibrePullback_maps fibrePullback_injects fibreAntichain_nonzero antichain_uniform_fibre_codes antichain_serial_embeds_product rigid_nonzero_serial
#classicism_types disjoint_equal_zero disjoint_lower_zero fibrePullback_maps fibrePullback_injects fibreAntichain_nonzero antichain_uniform_fibre_codes antichain_serial_embeds_product rigid_nonzero_serial
end Classicism.MathematicalContingency
