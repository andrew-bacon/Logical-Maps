import Classicism.Certified.Arithmetic
import Classicism.Results.Records.C5

/-!
# `C5` gives the Necessity of Arithmetic: the shallow steps

`c5-implies-necessity-of-arithmetic` (Bacon, *Could the truths of mathematics have been
different?*, Theorem 4.4, transposed to the map's numbers; see the write-up). The argument is an
induction on arithmetical sentences, whose steps are theorems of `C` or of `C5` with number
parameters: numbers are necessarily numbers; sums and products of numbers are necessary when
true (`C`) and, with `B`, impossible when false; identities and distinctnesses of numbers are
necessary (`NI`, `ND`); non-contingency passes through the connectives, and, with `BF` at the
type of numbers and `B`, through the quantifier restricted to numbers. Each is stated here as a
shallow theorem and derived, so that the metalogical induction over `AForm`
(`Results/SentenceSchemas/ArithmeticMeta.lean`) can compose their derivations.

Write `NC p` for `(p → □p) ∧ (¬p → □¬p)`, non-contingency, kept unfolded for the quoter.
-/

namespace Classicism
open Classicism.P

section shallow
variable {σ : Type} [Ty σ]

/-! ### Numbers -/

/-- `𝟎` is a number. -/
theorem arith_N_zero : Arith.N σ (Arith.zero σ) := finiteCardinality_zero

/-- The successor of a number is a number. -/
theorem arith_N_suc (n : Arith.ν σ) : Arith.N σ n → Arith.N σ (Arith.suc σ n) :=
  finiteCardinality_suc n

/-- **Numbers are necessarily numbers**, in `C`: the property `λn. □ℕn` holds of `𝟎`, since
`ℕ𝟎` is a theorem, and passes to successors by `K`, so every number has it. -/
theorem arith_N_box (n : Arith.ν σ) : Arith.N σ n → □ (Arith.N σ n) := fun hn =>
  hn (fun Z => □ (Arith.N σ Z))
    ⟨nec% (arith_N_zero (σ := σ)),
     fun Y hY => modal_K _ _ (nec% (arith_N_suc (σ := σ) Y)) hY⟩

/-- **Non-numbers are necessarily non-numbers**, given `B` as `◇□p → p`: a possible number is
possibly necessarily a number, hence a number. -/
theorem arith_N_box_not (hb : ∀ p : Prop, p → □ ◇ p) (n : Arith.ν σ) :
    ¬ Arith.N σ n → □ (¬ Arith.N σ n) := fun hn =>
  (em (□ (¬ Arith.N σ n))).elim id fun hnb =>
    (hn (Proofs.b_dia_box_imp hb _ (dia_mono _ _ (nec% (arith_N_box (σ := σ) n))
      (Eq.mpr (dia_eq_not_box_not _) hnb)))).elim

/-! ### Sums and products -/

/-- `Sum(m, 𝟎, m)`: the definition's consequent is its own antecedent. -/
theorem arith_Sum_zero (m : Arith.ν σ) : Arith.Sum σ m (Arith.zero σ) m := fun _ h0 _ => h0

/-- `Sum(m, i, j) → Sum(m, i⁺, j⁺)` for numbers `i`, `j`: the recursion clause. -/
theorem arith_Sum_step (m i j : Arith.ν σ) :
    Arith.N σ i → Arith.N σ j → Arith.Sum σ m i j → Arith.Sum σ m (Arith.suc σ i) (Arith.suc σ j) :=
  fun hi hj hs R h0 hstep => hstep i j hi hj (hs R h0 hstep)

/-- **Sums are necessary when true**, in `C`: instantiate the definition of `Sum(m, n, o)` at
the relation `λi j. □Sum(m, i, j)`, which holds at `(𝟎, m)` and is closed under the recursion
on numbers, numbers being necessarily numbers. -/
theorem arith_Sum_box (m n o : Arith.ν σ) : Arith.Sum σ m n o → □ (Arith.Sum σ m n o) := fun hs =>
  hs (fun i j => □ (Arith.Sum σ m i j)) (nec% (arith_Sum_zero (σ := σ) m))
    fun i j hi hj hij => modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (arith_Sum_step (σ := σ) m i j)) (arith_N_box i hi)) (arith_N_box j hj)) hij

/-- `Prod(m, 𝟎, 𝟎)`. -/
theorem arith_Prod_zero (m : Arith.ν σ) : Arith.Prod σ m (Arith.zero σ) (Arith.zero σ) :=
  fun _ h0 _ => h0

/-- The recursion clause of `Prod`. -/
theorem arith_Prod_step (m i j k : Arith.ν σ) :
    Arith.N σ i → Arith.N σ j → Arith.N σ k → Arith.Prod σ m i j → Arith.Sum σ m j k →
      Arith.Prod σ m (Arith.suc σ i) k :=
  fun hi hj hk hp hs R h0 hstep => hstep i j k hi hj hk (hp R h0 hstep) hs

/-- **Products are necessary when true**, in `C`, as for sums, with the sum in the recursion
clause necessary by the last. -/
theorem arith_Prod_box (m n o : Arith.ν σ) : Arith.Prod σ m n o → □ (Arith.Prod σ m n o) :=
  fun hp => hp (fun i j => □ (Arith.Prod σ m i j)) (nec% (arith_Prod_zero (σ := σ) m))
    fun i j k hi hj hk hij hs => modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (arith_Prod_step (σ := σ) m i j k)) (arith_N_box i hi)) (arith_N_box j hj))
      (arith_N_box k hk)) hij) (arith_Sum_box m j k hs)

/-- **Sums are impossible when false**, given `B`. -/
theorem arith_Sum_box_not (hb : ∀ p : Prop, p → □ ◇ p) (m n o : Arith.ν σ) :
    ¬ Arith.Sum σ m n o → □ (¬ Arith.Sum σ m n o) := fun hn =>
  (em (□ (¬ Arith.Sum σ m n o))).elim id fun hnb =>
    (hn (Proofs.b_dia_box_imp hb _ (dia_mono _ _ (nec% (arith_Sum_box (σ := σ) m n o))
      (Eq.mpr (dia_eq_not_box_not _) hnb)))).elim

/-- **Products are impossible when false**, given `B`. -/
theorem arith_Prod_box_not (hb : ∀ p : Prop, p → □ ◇ p) (m n o : Arith.ν σ) :
    ¬ Arith.Prod σ m n o → □ (¬ Arith.Prod σ m n o) := fun hn =>
  (em (□ (¬ Arith.Prod σ m n o))).elim id fun hnb =>
    (hn (Proofs.b_dia_box_imp hb _ (dia_mono _ _ (nec% (arith_Prod_box (σ := σ) m n o))
      (Eq.mpr (dia_eq_not_box_not _) hnb)))).elim

/-! ### The atomic formulas are non-contingent, on numbers -/

/-- `NC(ℕt)`, given `B`. -/
theorem arith_nc_N (hb : ∀ p : Prop, p → □ ◇ p) (n : Arith.ν σ) :
    (Arith.N σ n → □ (Arith.N σ n)) ∧ (¬ Arith.N σ n → □ (¬ Arith.N σ n)) :=
  ⟨arith_N_box n, arith_N_box_not hb n⟩

/-- `NC(Sum(m, n, o))`, given `B`. -/
theorem arith_nc_Sum (hb : ∀ p : Prop, p → □ ◇ p) (m n o : Arith.ν σ) :
    (Arith.Sum σ m n o → □ (Arith.Sum σ m n o)) ∧ (¬ Arith.Sum σ m n o → □ (¬ Arith.Sum σ m n o)) :=
  ⟨arith_Sum_box m n o, arith_Sum_box_not hb m n o⟩

/-- `NC(Prod(m, n, o))`, given `B`. -/
theorem arith_nc_Prod (hb : ∀ p : Prop, p → □ ◇ p) (m n o : Arith.ν σ) :
    (Arith.Prod σ m n o → □ (Arith.Prod σ m n o)) ∧
      (¬ Arith.Prod σ m n o → □ (¬ Arith.Prod σ m n o)) :=
  ⟨arith_Prod_box m n o, arith_Prod_box_not hb m n o⟩

/-- `NC(m = n)`, given `ND` at the type of numbers (`NI` for the other half). -/
theorem arith_nc_eq (nd : ∀ x y : Arith.ν σ, x ≠ y → □ (x ≠ y)) (m n : Arith.ν σ) :
    (m = n → □ (m = n)) ∧ (m ≠ n → □ (m ≠ n)) :=
  ⟨necessity_of_identity m n, nd m n⟩

/-! ### Non-contingency through the connectives and the number quantifier -/

/-- `NC p → NC ¬p`. -/
theorem nc_neg (p : Prop) :
    ((p → □ p) ∧ (¬ p → □ ¬ p)) → ((¬ p → □ ¬ p) ∧ (¬ ¬ p → □ ¬ ¬ p)) := fun h =>
  ⟨h.2, fun hnn => modal_K _ _ (nec% (fun (hp : p) (hn : ¬ p) => hn hp))
    (h.1 ((em p).elim id fun hn => (hnn hn).elim))⟩

/-- `NC p → NC q → NC (p ∧ q)`. -/
theorem nc_conj (p q : Prop) :
    ((p → □ p) ∧ (¬ p → □ ¬ p)) → ((q → □ q) ∧ (¬ q → □ ¬ q)) →
      ((p ∧ q → □ (p ∧ q)) ∧ (¬ (p ∧ q) → □ ¬ (p ∧ q))) := fun hp hq =>
  ⟨fun h => modal_K _ _ (modal_K _ _ (nec% (fun (a : p) (b : q) => (⟨a, b⟩ : p ∧ q)))
      (hp.1 h.1)) (hq.1 h.2),
   fun hn => (em p).elim
     (fun a => (em q).elim (fun b => (hn ⟨a, b⟩).elim)
       (fun nb => modal_K _ _ (nec% (fun (nb : ¬ q) (h : p ∧ q) => nb h.2)) (hq.2 nb)))
     (fun na => modal_K _ _ (nec% (fun (na : ¬ p) (h : p ∧ q) => na h.1)) (hp.2 na))⟩

/-- `NC p → NC q → NC (p ∨ q)`. -/
theorem nc_disj (p q : Prop) :
    ((p → □ p) ∧ (¬ p → □ ¬ p)) → ((q → □ q) ∧ (¬ q → □ ¬ q)) →
      ((p ∨ q → □ (p ∨ q)) ∧ (¬ (p ∨ q) → □ ¬ (p ∨ q))) := fun hp hq =>
  ⟨fun h => h.elim
     (fun a => modal_K _ _ (nec% (fun (a : p) => (Or.inl a : p ∨ q))) (hp.1 a))
     (fun b => modal_K _ _ (nec% (fun (b : q) => (Or.inr b : p ∨ q))) (hq.1 b)),
   fun hn => modal_K _ _ (modal_K _ _
     (nec% (fun (na : ¬ p) (nb : ¬ q) (h : p ∨ q) => h.elim na nb))
     (hp.2 fun a => hn (Or.inl a))) (hq.2 fun b => hn (Or.inr b))⟩

/-- **The quantifier step**: if `NC(Xv)` for every number `v`, then `NC(∀v ∈ ℕ. Xv)`, given
`BF` at the type of numbers and `B` (for non-numbers being necessarily non-numbers). -/
theorem nc_all (bf : ∀ X : Arith.ν σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (hb : ∀ p : Prop, p → □ ◇ p) (X : Arith.ν σ → Prop)
    (h : ∀ v, Arith.N σ v → (X v → □ (X v)) ∧ (¬ X v → □ ¬ X v)) :
    ((∀ v, Arith.N σ v → X v) → □ (∀ v, Arith.N σ v → X v)) ∧
      (¬ (∀ v, Arith.N σ v → X v) → □ ¬ (∀ v, Arith.N σ v → X v)) :=
  ⟨fun hall => bf (fun v => Arith.N σ v → X v) fun v => (em (Arith.N σ v)).elim
      (fun hv => modal_K _ _ (nec% (fun (hx : X v) (_ : Arith.N σ v) => hx))
        ((h v hv).1 (hall v hv)))
      (fun hv => modal_K _ _
        (nec% (fun (hn : ¬ Arith.N σ v) (hv' : Arith.N σ v) => ((hn hv').elim : X v)))
        (arith_N_box_not hb v hv)),
   fun hn => (em (∃ v, Arith.N σ v ∧ ¬ X v)).elim
     (fun he => he.elim fun v hv => modal_K _ _ (modal_K _ _
       (nec% (fun (a : Arith.N σ v) (b : ¬ X v) (hall : ∀ v, Arith.N σ v → X v) => b (hall v a)))
       (arith_N_box v hv.1)) ((h v hv.1).2 hv.2))
     (fun hne => (hn fun v hv => (em (X v)).elim id fun hx => (hne ⟨v, hv, hx⟩).elim).elim)⟩

/-- **The last step**: a non-contingent `p` is necessary or impossible, so `□(i → p)` or
`□(i → ¬p)` for any `i`. -/
theorem nc_final (p i : Prop) : ((p → □ p) ∧ (¬ p → □ ¬ p)) → □ (i → p) ∨ □ (i → ¬ p) := fun h =>
  (em p).elim (fun hp => Or.inl (modal_K _ _ (nec% (fun (hp : p) (_ : i) => hp)) (h.1 hp)))
    (fun hn => Or.inr (modal_K _ _ (nec% (fun (hn : ¬ p) (_ : i) => hn)) (h.2 hn)))

/-! ### `C5` supplies `B`, `BF` at the type of numbers and `ND` there -/

/-- `B`, from `□ND` at `t`. -/
theorem c5_b : NecNecessityOfDistinctness Prop → ∀ p : Prop, p → □ ◇ p := fun hnd =>
  Proofs.b_of_nd_t (box_elim hnd)

/-- `BF` at the type of numbers, from `□ND` at `t`. -/
theorem c5_bf_nu : NecNecessityOfDistinctness Prop →
    ∀ X : Arith.ν σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x) := Proofs.bf_of_box_nd_t

/-- `ND` at the type of numbers, from `□ND` at `t`. -/
theorem c5_nd_nu : NecNecessityOfDistinctness Prop → ∀ x y : Arith.ν σ, x ≠ y → □ (x ≠ y) :=
  fun hnd => Proofs.nd_of_nd_t (box_elim hnd)

/-! ### The vocabulary as variables

The metalogical induction instantiates each step at the quoted vocabulary, `ℕ`, `𝟎`, `Suc`,
`Sum` and `Prod` as closed terms (`Arith.N.term σ` and the rest). The steps it composes
therefore take the vocabulary as variables equal to the definitions: quoted, an equation's
right side is the quoted definition itself, and reflexivity discharges it. Quoting `ℕt` by its
unfolded body instead would need a β-conversion at every atom. Object variables come first,
then the modal hypotheses, then the equations, then any inductive hypothesis. -/

/-- `𝟎` is a number, with the vocabulary as variables. -/
theorem arith_N_zero_rel (N : Arith.ν σ → Prop) (z : Arith.ν σ)
    (hN : N = Arith.N σ) (hz : z = Arith.zero σ) : N z :=
  Eq.mpr (congrArg (fun X : Arith.ν σ → Prop => X z) hN)
    (Eq.mpr (congrArg (fun y : Arith.ν σ => Arith.N σ y) hz) arith_N_zero)

/-- The successor of a number is a number, with the vocabulary as variables. -/
theorem arith_N_suc_rel (N : Arith.ν σ → Prop) (s : Arith.ν σ → Arith.ν σ) (n : Arith.ν σ)
    (hN : N = Arith.N σ) (hs : s = Arith.suc σ) : N n → N (s n) :=
  Eq.mpr (congrArg (fun X : Arith.ν σ → Prop => X n → X (s n)) hN)
    (Eq.mpr (congrArg (fun f : Arith.ν σ → Arith.ν σ => Arith.N σ n → Arith.N σ (f n)) hs)
      (arith_N_suc n))

/-- `NC(ℕn)`, with the vocabulary as variables. -/
theorem arith_nc_N_rel (N : Arith.ν σ → Prop) (n : Arith.ν σ) (hb : ∀ p : Prop, p → □ ◇ p)
    (hN : N = Arith.N σ) : (N n → □ (N n)) ∧ (¬ N n → □ (¬ N n)) :=
  Eq.mpr (congrArg (fun X : Arith.ν σ → Prop => (X n → □ (X n)) ∧ (¬ X n → □ (¬ X n))) hN)
    (arith_nc_N hb n)

/-- `NC(Sum(m, n, o))`, with the vocabulary as variables. -/
theorem arith_nc_Sum_rel (S : Arith.ν σ → Arith.ν σ → Arith.ν σ → Prop) (m n o : Arith.ν σ)
    (hb : ∀ p : Prop, p → □ ◇ p) (hS : S = Arith.Sum σ) :
    (S m n o → □ (S m n o)) ∧ (¬ S m n o → □ (¬ S m n o)) :=
  Eq.mpr (congrArg (fun R : Arith.ν σ → Arith.ν σ → Arith.ν σ → Prop =>
    (R m n o → □ (R m n o)) ∧ (¬ R m n o → □ (¬ R m n o))) hS) (arith_nc_Sum hb m n o)

/-- `NC(Prod(m, n, o))`, with the vocabulary as variables. -/
theorem arith_nc_Prod_rel (Pr : Arith.ν σ → Arith.ν σ → Arith.ν σ → Prop) (m n o : Arith.ν σ)
    (hb : ∀ p : Prop, p → □ ◇ p) (hP : Pr = Arith.Prod σ) :
    (Pr m n o → □ (Pr m n o)) ∧ (¬ Pr m n o → □ (¬ Pr m n o)) :=
  Eq.mpr (congrArg (fun R : Arith.ν σ → Arith.ν σ → Arith.ν σ → Prop =>
    (R m n o → □ (R m n o)) ∧ (¬ R m n o → □ (¬ R m n o))) hP) (arith_nc_Prod hb m n o)

/-- The quantifier step, with the vocabulary as variables. -/
theorem nc_all_rel (N : Arith.ν σ → Prop) (X : Arith.ν σ → Prop)
    (bf : ∀ X : Arith.ν σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (hb : ∀ p : Prop, p → □ ◇ p) (hN : N = Arith.N σ)
    (h : ∀ v, N v → (X v → □ (X v)) ∧ (¬ X v → □ ¬ X v)) :
    ((∀ v, N v → X v) → □ (∀ v, N v → X v)) ∧
      (¬ (∀ v, N v → X v) → □ ¬ (∀ v, N v → X v)) :=
  Eq.mpr (congrArg (fun M : Arith.ν σ → Prop =>
      (∀ v, M v → (X v → □ (X v)) ∧ (¬ X v → □ ¬ X v)) →
        ((∀ v, M v → X v) → □ (∀ v, M v → X v)) ∧
          (¬ (∀ v, M v → X v) → □ ¬ (∀ v, M v → X v))) hN)
    (nc_all bf hb X) h

end shallow

#classicism_derive Classicism.arith_N_zero_rel Classicism.arith_N_suc_rel
  Classicism.arith_nc_N_rel Classicism.arith_nc_Sum_rel Classicism.arith_nc_Prod_rel
  Classicism.arith_nc_eq Classicism.nc_neg Classicism.nc_conj Classicism.nc_disj
  Classicism.nc_all_rel Classicism.nc_final Classicism.c5_b Classicism.c5_bf_nu Classicism.c5_nd_nu

end Classicism
