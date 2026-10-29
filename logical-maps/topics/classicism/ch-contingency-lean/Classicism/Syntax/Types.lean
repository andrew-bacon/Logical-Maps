/-!
# The metalogical layer: types of the relational type system

This is the first module of the **metalogical layer**, in which the terms of the paper's
object language, their derivations, and their models are objects of Lean, so that
metalogical statements can be made about them: that a schema implies a schema, that a
closed pure sentence is a theorem, that a sentence holds in a model. The shallow and
strict layers state and prove object-language theorems *in* Lean; this layer states
theorems *about* the object language, and is related to the other two by a denotation
that reads its terms as Lean propositions.

The types are the relational type system `R` (Classicism, §1.1): two base types, `e` and
`t`, and `σ → τ` for a type `σ` and a *relational* type `τ`, a relational type being one
that ends in `t`. The definition is the mutual one of Dorr's *Elimination*, Appendix A:
types and terminals, with terminals subsumed under types.

Only these two base types: the type system is not parametrized by a set of base types,
and nonlogical vocabulary enters through a signature of constants instead.

## Type variables

Besides the paper's types there are **type variables**, `Ty.var i`: types about which
nothing is known. A type variable is never relational, so it can be the type of a variable
or the argument type of an arrow but never a codomain. Since application and abstraction
always produce relational types, the only terms of a variable type are variables (and
constants of a signature that gives one that type, which the vectorization theorem rules
out). A type with no type variable is **closed**; the closed types are the paper's, and the
map's schemas range over them.

Type variables are a device of the metalogic. A derivation at a type variable uses
nothing about that type, so it can be carried to any type, and to any *list* of types,
a variable of the type becoming a block of variables (`Syntax/Vectorize.lean`). A type
*parameter*, by contrast, is a variable of Lean, `σ : Ty`, ranging over all types; a
proof of `∀ σ : Ty, …` may split on `σ`, and says nothing about uniformity. The
translator's derivations are uniform, so they can be instantiated at a type variable, and
that is how every certified result gets its list form (`VECTORIZATION-PLAN.md`).
-/

namespace Classicism.Meta

mutual
  /-- A type of `R`: the type `e` of individuals, a relational type, or a type variable. -/
  inductive Ty : Type
    | e : Ty
    | rel : RTy → Ty
    /-- A type variable: a type about which nothing is known, never relational. -/
    | var : Nat → Ty
  /-- A relational type, one ending in `t`: `t` itself, or `σ → ρ` for a type `σ` and a
  relational type `ρ`. -/
  inductive RTy : Type
    | t : RTy
    /-- `σ → ρ`, for a type `σ` and a relational type `ρ`. -/
    | arr : Ty → RTy → RTy
end

/-- `σ ⇒ ρ` is the relational type `σ → ρ`; right-associative, as arrows are. -/
infixr:60 " ⇒ " => RTy.arr

instance : Coe RTy Ty := ⟨Ty.rel⟩

/-- The type `t` of propositions, as a type. -/
abbrev Ty.t : Ty := Ty.rel RTy.t

mutual
  /-- Decidable equality on types. -/
  def Ty.beq : Ty → Ty → Bool
    | .e, .e => true
    | .rel ρ, .rel ρ' => RTy.beq ρ ρ'
    | .var i, .var j => i == j
    | _, _ => false
  /-- Decidable equality on relational types. -/
  def RTy.beq : RTy → RTy → Bool
    | .t, .t => true
    | .arr σ ρ, .arr σ' ρ' => Ty.beq σ σ' && RTy.beq ρ ρ'
    | _, _ => false
end

mutual
  theorem Ty.eq_of_beq : ∀ {σ σ' : Ty}, Ty.beq σ σ' = true → σ = σ'
    | .e, .e, _ => rfl
    | .rel _, .rel _, h => congrArg Ty.rel (RTy.eq_of_beq h)
    | .var _, .var _, h => congrArg Ty.var (by simpa [Ty.beq] using h)
  theorem RTy.eq_of_beq : ∀ {ρ ρ' : RTy}, RTy.beq ρ ρ' = true → ρ = ρ'
    | .t, .t, _ => rfl
    | .arr _ _, .arr _ _, h => by
      simp only [RTy.beq, Bool.and_eq_true] at h
      rw [Ty.eq_of_beq h.1, RTy.eq_of_beq h.2]
end

mutual
  theorem Ty.beq_self : ∀ σ : Ty, Ty.beq σ σ = true
    | .e => rfl
    | .rel ρ => RTy.beq_self ρ
    | .var _ => by simp [Ty.beq]
  theorem RTy.beq_self : ∀ ρ : RTy, RTy.beq ρ ρ = true
    | .t => rfl
    | .arr σ ρ => by simp only [RTy.beq, Bool.and_eq_true]; exact ⟨Ty.beq_self σ, RTy.beq_self ρ⟩
end

instance : DecidableEq Ty := fun σ σ' =>
  if h : Ty.beq σ σ' = true then isTrue (Ty.eq_of_beq h)
  else isFalse fun e => h (e ▸ Ty.beq_self σ)

instance : DecidableEq RTy := fun ρ ρ' =>
  if h : RTy.beq ρ ρ' = true then isTrue (RTy.eq_of_beq h)
  else isFalse fun e => h (e ▸ RTy.beq_self ρ)

theorem Ty.rel_injective {ρ ρ' : RTy} (h : Ty.rel ρ = Ty.rel ρ') : ρ = ρ' :=
  Ty.rel.inj h

/-- The arity of a relational type: `t` has arity `0`, `σ → ρ` one more than `ρ`. -/
def RTy.arity : RTy → Nat
  | .t => 0
  | .arr _ ρ => ρ.arity + 1

/-- The argument types of a relational type, in order. -/
def RTy.args : RTy → List Ty
  | .t => []
  | .arr σ ρ => σ :: ρ.args

/-- `σs ⇒* ρ`, the relational type `σ₁ → … → σₙ → ρ`: the type of a function of the
arguments `σs` into `ρ`. Reducible, so that `(σ :: σs) ⇒* ρ` is `σ ⇒ (σs ⇒* ρ)` to `rw` and
`simp` as well as to the kernel. -/
@[reducible] def RTy.arrs : List Ty → RTy → RTy
  | [], ρ => ρ
  | σ :: σs, ρ => .arr σ (arrs σs ρ)

@[inherit_doc] infixr:60 " ⇒* " => RTy.arrs

@[simp] theorem RTy.arrs_nil (ρ : RTy) : ([] : List Ty) ⇒* ρ = ρ := rfl
@[simp] theorem RTy.arrs_cons (σ : Ty) (σs : List Ty) (ρ : RTy) :
    (σ :: σs) ⇒* ρ = σ ⇒ (σs ⇒* ρ) := rfl

theorem RTy.arrs_append (σs σs' : List Ty) (ρ : RTy) :
    (σs ++ σs') ⇒* ρ = σs ⇒* (σs' ⇒* ρ) := by
  induction σs with
  | nil => rfl
  | cons σ σs ih => simp [ih]

/-- The relational type with the given argument types: `σ₁ → … → σₙ → t`. -/
abbrev RTy.ofArgs (σs : List Ty) : RTy := σs ⇒* .t

theorem RTy.ofArgs_args : ∀ ρ : RTy, RTy.ofArgs ρ.args = ρ
  | .t => rfl
  | .arr σ ρ => by simp [RTy.args, RTy.ofArgs_args ρ]

/-- Induction on a relational type alone, the mutual motive on `Ty` being trivial: a
property of relational types that holds at `t` and passes from `ρ` to `σ → ρ` holds of
all of them. This is the induction on the structure of types that the shallow layer
cannot perform, where `Rel` is a class and not a code. -/
theorem RTy.induction {motive : RTy → Prop} (t : motive .t)
    (arr : ∀ σ ρ, motive ρ → motive (.arr σ ρ)) : ∀ ρ, motive ρ :=
  fun ρ => RTy.rec (motive_1 := fun _ => True) (motive_2 := motive)
    trivial (fun _ _ => trivial) (fun _ => trivial) t (fun σ ρ _ ih => arr σ ρ ih) ρ

/-- Every type of `R` is `e`, `σ₁ → … → σₙ → t`, or a type variable; this is the case
split the shallow layer could not perform, since there `Rel` is a class and not a code. -/
theorem Ty.cases (σ : Ty) :
    σ = Ty.e ∨ (∃ σs : List Ty, σ = Ty.rel (RTy.ofArgs σs)) ∨ ∃ i, σ = Ty.var i := by
  cases σ with
  | e => exact Or.inl rfl
  | rel ρ => exact Or.inr (Or.inl ⟨ρ.args, by rw [RTy.ofArgs_args]⟩)
  | var i => exact Or.inr (Or.inr ⟨i, rfl⟩)

/-! ### Closed types -/

mutual
  /-- A type is **closed** when it contains no type variable: a type of the paper's
  language. -/
  def Ty.Closed : Ty → Prop
    | .e => True
    | .rel ρ => ρ.Closed
    | .var _ => False
  /-- A relational type is closed when it contains no type variable. -/
  def RTy.Closed : RTy → Prop
    | .t => True
    | .arr σ ρ => σ.Closed ∧ ρ.Closed
end

@[simp] theorem Ty.closed_e : Ty.e.Closed := trivial
@[simp] theorem Ty.closed_rel (ρ : RTy) : (Ty.rel ρ).Closed ↔ ρ.Closed := Iff.rfl
@[simp] theorem Ty.not_closed_var (i : Nat) : ¬ (Ty.var i).Closed := id
@[simp] theorem RTy.closed_t : RTy.t.Closed := trivial
@[simp] theorem RTy.closed_arr (σ : Ty) (ρ : RTy) : (σ ⇒ ρ).Closed ↔ σ.Closed ∧ ρ.Closed :=
  Iff.rfl

theorem RTy.closed_arrs (σs : List Ty) (ρ : RTy) :
    (σs ⇒* ρ).Closed ↔ (∀ σ ∈ σs, σ.Closed) ∧ ρ.Closed := by
  induction σs with
  | nil => simp
  | cons σ σs ih => simp [ih, and_assoc]

theorem RTy.closed_args : ∀ {ρ : RTy}, ρ.Closed → ∀ σ ∈ ρ.args, σ.Closed
  | .t, _ => by simp [RTy.args]
  | .arr σ ρ, h => by
    simp only [RTy.args, List.mem_cons, forall_eq_or_imp]
    exact ⟨h.1, RTy.closed_args h.2⟩

mutual
  /-- Closedness of a type is decidable. -/
  def Ty.decClosed : ∀ σ : Ty, Decidable σ.Closed
    | .e => isTrue trivial
    | .rel ρ => RTy.decClosed ρ
    | .var _ => isFalse id
  /-- Closedness of a relational type is decidable. -/
  def RTy.decClosed : ∀ ρ : RTy, Decidable ρ.Closed
    | .t => isTrue trivial
    | .arr σ ρ =>
      match Ty.decClosed σ, RTy.decClosed ρ with
      | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
      | isFalse h₁, _ => isFalse fun h => h₁ h.1
      | _, isFalse h₂ => isFalse fun h => h₂ h.2
end

instance (σ : Ty) : Decidable σ.Closed := Ty.decClosed σ
instance (ρ : RTy) : Decidable ρ.Closed := RTy.decClosed ρ

end Classicism.Meta
