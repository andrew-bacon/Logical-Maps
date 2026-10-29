import Classicism.Results.MathematicalContingency.BitCharacteristics
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α σ τ : Type} [Ty α] [Ty σ] [Ty τ]

theorem restricted_pointwise_coext (A X S : α → Prop) (q : Prop) (hA : Rigid A)
    (hX : □ (∀ n, X n → A n)) (hS : □ (∀ n, S n → A n))
    (pointwise : ∀ n, A n → EntailmentOrder q (X n ↔ S n)) : EntailmentOrder q (X ≡ S) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (h : ∀ n, A n → q → (X n ↔ S n))
      (hx : ∀ n, X n → A n) (hs : ∀ n, S n → A n) (hq : q) n =>
        (show X n ↔ S n from ⟨fun hxn => (h n (hx n hxn) hq).mp hxn,
          fun hsn => (h n (hs n hsn) hq).mpr hsn⟩)))
    (restricted_barcan_unary A (fun n => q → (X n ↔ S n)) hA pointwise)) hX) hS

theorem countable_whole_row_coext (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rigidN : Rigid (@LowerNat σ _))
    (C : CountableBitGraph σ τ → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (laws : CountableCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (d : CountableBitGraph σ τ) (q : Prop) (hd : CountableBitCarrier I d) (hc : C d q)
    (a : τ) (X S : ((σ → Prop) → Prop) → Prop)
    (hx : IndexedName LowerNat I T a X) (hs : RigidPower LowerNat S)
    (row : ∀ n b, CharacteristicBits LowerNat S n b → d n a b) : EntailmentOrder q (X ≡ S) := by
  apply restricted_pointwise_coext LowerNat X S q rigidN hx.2.1
    (restricted_barcan_unary S LowerNat hs.1 (fun n hn => box_elim rigidN.1 n (hs.2 n hn)))
  intro n hn
  obtain ⟨p,ht⟩ := total a n hx.1 hn
  have ev := hx.2.2 n hn p ht
  obtain h | h := em (S n)
  · have hp : EntailmentOrder q (X n) := ev.symm ▸
      laws.1 d q n a p hd hc ht (row n True ⟨hn,Or.inl ⟨h,rfl⟩⟩)
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hp : q → X n) (hs : S n) (hq : q) =>
        (show X n ↔ S n from ⟨fun _ => hs,fun _ => hp hq⟩))) hp) (box_elim hs.1.1 n h)
  · have hp : EntailmentOrder q (¬ X n) := ev.symm ▸
      laws.2 d q n a p hd hc ht (row n False ⟨hn,Or.inr ⟨h,rfl⟩⟩)
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hp : q → ¬ X n) (hs : ¬ S n) (hq : q) =>
        (show X n ↔ S n from ⟨fun hx => (hp hq hx).elim,fun hx => (hs hx).elim⟩))) hp)
      (rigid_subset_negative LowerNat S (lowerNat_nd hi) hs.1 hs.2 n hn h)

#classicism_check restricted_pointwise_coext countable_whole_row_coext
#classicism_types restricted_pointwise_coext countable_whole_row_coext
end Classicism.MathematicalContingency
