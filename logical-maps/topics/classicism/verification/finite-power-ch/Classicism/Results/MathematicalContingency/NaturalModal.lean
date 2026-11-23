import Classicism.Results.MathematicalContingency.Arithmetic

/-!
Modal facts for the paper's at-least natural numbers.
Formalization: OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
The persistence arguments adapt Classicism.arith_N_box / arith_Sum_box /
arith_Prod_box from the upstream exact-cardinality presentation.
Rigidity of LowerNat remains an explicit deferred hypothesis, never an axiom.
-/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem lowerNat_box (n : (σ → Prop) → Prop) (hn : LowerNat n) : □ (LowerNat n) :=
  hn (fun m => □ (LowerNat m))
    ⟨nec% (lowerNat_zero (σ := σ)),
     fun m hm => modal_K _ _ (nec% (lowerNat_suc m)) hm⟩

theorem lowerNat_zero_ne_suc_necessary (hi : DraftBoxInfinity σ)
    (n : (σ → Prop) → Prop) (hn : LowerNat n) : □ (AtLeastZero σ ≠ SucCard n) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (hp : LowerPeano σ) (hn : LowerNat n) => hp.1 n hn)) hi) (lowerNat_box n hn)

theorem lowerNat_suc_ne_necessary (hi : DraftBoxInfinity σ)
    (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n)
    (hne : □ (m ≠ n)) : □ (SucCard m ≠ SucCard n) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hp : LowerPeano σ) (hm : LowerNat m) (hn : LowerNat n)
      (h : m ≠ n) (he : SucCard m = SucCard n) => h (hp.2 m n hm hn he))) hi)
      (lowerNat_box m hm)) (lowerNat_box n hn)) hne

/-- ND is proved from necessary Peano laws; no global ND or modal B is used. -/
theorem lowerNat_nd (hi : DraftBoxInfinity σ)
    (m n : (σ → Prop) → Prop) (hm : LowerNat m) (hn : LowerNat n)
    (hne : m ≠ n) : □ (m ≠ n) := by
  have h : ∀ (m : (σ → Prop) → Prop), LowerNat m → ∀ (n : (σ → Prop) → Prop), LowerNat n → m ≠ n → □ (m ≠ n) := by
    intro m hm
    apply lowerNat_induction _ ?_ ?_ m hm
    · intro n hn hne
      obtain he | ⟨k,hk,he⟩ := lowerNat_cases n hn
      · exact (hne he.symm).elim
      · subst n
        exact lowerNat_zero_ne_suc_necessary hi k hk
    · intro k hk ih n hn hne
      obtain he | ⟨l,hl,he⟩ := lowerNat_cases n hn
      · subst n
        exact modal_K _ _ (nec% (fun (h : AtLeastZero σ ≠ SucCard k)
          (e : SucCard k = AtLeastZero σ) => h e.symm))
          (lowerNat_zero_ne_suc_necessary hi k hk)
      · subst n
        exact lowerNat_suc_ne_necessary hi k l hk hl
          (ih l hl (fun e => hne (congrArg SucCard e)))
  exact h m hm n hn hne

theorem lowerSum_box (m n k : (σ → Prop) → Prop) (hs : LowerSum m n k) :
    □ (LowerSum m n k) :=
  hs (fun a b => □ (LowerSum m a b)) (nec% (lowerSum_zero m))
    (fun a b ha hb h => modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (lowerSum_suc m a b)) (lowerNat_box a ha)) (lowerNat_box b hb)) h)

theorem lowerProd_box (m n k : (σ → Prop) → Prop) (hp : LowerProd m n k) :
    □ (LowerProd m n k) :=
  hp (fun a b => □ (LowerProd m a b)) (nec% (lowerProd_zero m))
    (fun a b c ha hb hc h hs => modal_K _ _ (modal_K _ _ (modal_K _ _
      (modal_K _ _ (modal_K _ _ (nec% (lowerProd_suc m a b c))
        (lowerNat_box a ha)) (lowerNat_box b hb)) (lowerNat_box c hc)) h)
          (lowerSum_box m b c hs))

/-- The name lemma is now available on N, conditional only on the explicitly
deferred rigidity result and the displayed RC / Infinity instances. -/
theorem lowerNat_name_representation
    (rigidN : Rigid (@LowerNat σ _)) (hi : DraftBoxInfinity σ)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (T : ((σ → Prop) → Prop) → Prop → Prop)
    (total : ∀ n, LowerNat n → ∃ p, T n p)
    (functional : ∀ n, LowerNat n → ∀ p q, T n p → T n q → p = q) :
    ∃ X, RepresentsOn LowerNat T X ∧ ∀ Y, RepresentsOn LowerNat T Y → Y = X :=
  restricted_name_representation rc LowerNat T rigidN (fun m n hm hn => lowerNat_nd hi m n hm hn)
    total functional

#classicism_check lowerNat_box lowerNat_zero_ne_suc_necessary lowerNat_suc_ne_necessary
  lowerNat_nd lowerSum_box lowerProd_box lowerNat_name_representation
#classicism_types lowerNat_box lowerNat_zero_ne_suc_necessary lowerNat_suc_ne_necessary
  lowerNat_nd lowerSum_box lowerProd_box lowerNat_name_representation
end Classicism.MathematicalContingency
