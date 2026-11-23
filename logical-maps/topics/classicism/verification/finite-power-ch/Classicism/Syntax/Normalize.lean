import Classicism.Syntax.Conversion

/-!
# A verified βη-normalizer

`Term.nf n t` performs `n` passes of parallel β-reduction on `t`, with η at each
abstraction,, and `Conv.nf` proves
that a term converts to its normal form. So two terms whose normal forms coincide are
convertible by one lemma, `Conv.of_nf`, whose hypothesis the kernel discharges by
evaluation: `Conv.of_nf n a b rfl`.

This is the reflection pattern once more, here for conversion. The translator needs a
conversion proof at every point where Lean's kernel silently β-reduced, and building those
as explicit chains of `Conv.beta` and congruences made the derivations large and slow to
check. With this lemma a conversion proof is three words.

Both β and η are normalized: the quoters η-reduce at the source, and the axioms as
written by hand do not, so `(λpq. p ∧ q)` and `∧` have to meet.
-/

namespace Classicism.Meta

variable {Sig : Signature}

namespace Term

/-- Apply a function to an argument, contracting the redex if the function is an
abstraction. -/
def apply {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig Γ (σ ⇒ ρ) → Term Sig Γ σ → Term Sig Γ ρ
  | .lam b, a => b.instantiate a
  | f, a => .app f a

theorem conv_apply {Γ : Ctx} {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    Term.app f a ≡ apply f a := by
  unfold apply
  split
  · exact Conv.beta _ _
  · exact Conv.refl _

/-! ### Strengthening, for η

`λ. F 0` is an η-redex when `F` does not mention the variable `0`, which is to say when
`F` is the weakening of some `G`; then it converts to `G`. `strengthen?` finds `G`: it is
the partial inverse of weakening, a partial renaming lifted through binders. -/

/-- A partial renaming: a variable may have no image. -/
def PRen (Γ Δ : Ctx) : Type := ∀ σ : Ty, Var Γ σ → Option (Var Δ σ)

/-- Push a partial renaming under a binder. -/
def PRen.lift {Γ Δ : Ctx} (r : PRen Γ Δ) {σ : Ty} : PRen (σ :: Γ) (σ :: Δ)
  | _, .zero => some .zero
  | _, .succ v => (r _ v).map .succ

/-- Rename along a partial renaming, by structural recursion: the implementation of
`prename`. -/
def prenameImpl : ∀ {Γ Δ : Ctx}, PRen Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Option (Term Sig Δ σ)
  | _, _, r, _, .var v => (r _ v).map .var
  | _, _, _, _, .const c => some (.const c)
  | _, _, r, _, .app f a => (prenameImpl r f).bind fun f' => (prenameImpl r a).bind fun a' => some (.app f' a')
  | _, _, r, _, .lam b => (prenameImpl (PRen.lift r) b).bind fun b' => some (.lam b')
  | _, _, _, _, .and => some .and
  | _, _, _, _, .or => some .or
  | _, _, _, _, .not => some .not
  | _, _, _, _, .all σ => some (.all σ)
  | _, _, _, _, .ex σ => some (.ex σ)
  | _, _, _, _, .eq σ => some (.eq σ)
  | _, _, _, _, .constR ρ => some (.constR ρ)
  | _, _, _, _, .negR ρ => some (.negR ρ)
  | _, _, _, _, .andR ρ => some (.andR ρ)
  | _, _, _, _, .orR ρ => some (.orR ρ)
  | _, _, _, _, .coextR ρ => some (.coextR ρ)
  | _, _, _, _, .boxR ρ => some (.boxR ρ)
  | _, _, _, _, .inclR ρ => some (.inclR ρ)

/-- Rename along a partial renaming, failing if a variable has no image. Through
`Term.rec`, as `Term.rename` is: the kernel evaluates it in the translator's
conversion proofs. -/
@[implemented_by prenameImpl]
def prename : ∀ {Γ Δ : Ctx}, PRen Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Option (Term Sig Δ σ) :=
  fun {_ Δ} r {_} t =>
    Term.rec (motive := fun Γ σ _ => ∀ Δ : Ctx, PRen Γ Δ → Option (Term Sig Δ σ))
      (var := fun v _ r => (r _ v).map Term.var)
      (const := fun c _ _ => some (Term.const c))
      (app := fun _ _ f a Δ' r => (f Δ' r).bind fun f' => (a Δ' r).bind fun a' => some (Term.app f' a'))
      (lam := fun _ b _ r => (b _ (PRen.lift r)).bind fun b' => some (Term.lam b'))
      (and := fun _ _ => some Term.and) (or := fun _ _ => some Term.or)
      (not := fun _ _ => some Term.not) (all := fun σ _ _ => some (Term.all σ))
      (ex := fun σ _ _ => some (Term.ex σ)) (eq := fun σ _ _ => some (Term.eq σ))
      (constR := fun ρ _ _ => some (Term.constR ρ)) (negR := fun ρ _ _ => some (Term.negR ρ))
      (andR := fun ρ _ _ => some (Term.andR ρ)) (orR := fun ρ _ _ => some (Term.orR ρ))
      (coextR := fun ρ _ _ => some (Term.coextR ρ)) (boxR := fun ρ _ _ => some (Term.boxR ρ))
      (inclR := fun ρ _ _ => some (Term.inclR ρ))
      t Δ r

section
variable {Γ Δ : Ctx} (r : PRen Γ Δ)
@[simp] theorem prename_var {σ : Ty} (v : Var Γ σ) :
    prename (Sig := Sig) r (.var v) = (r _ v).map .var := rfl
@[simp] theorem prename_const (c : Sig.Const) : prename r (.const c) = some (.const c) := rfl
@[simp] theorem prename_app {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    prename r (.app f a) = (prename r f).bind fun f' => (prename r a).bind fun a' => some (.app f' a') := rfl
@[simp] theorem prename_lam {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    prename r (.lam b) = (prename (PRen.lift r) b).bind fun b' => some (.lam b') := rfl
@[simp] theorem prename_and : prename (Sig := Sig) r .and = some .and := rfl
@[simp] theorem prename_or : prename (Sig := Sig) r .or = some .or := rfl
@[simp] theorem prename_not : prename (Sig := Sig) r .not = some .not := rfl
@[simp] theorem prename_all (σ : Ty) : prename (Sig := Sig) r (.all σ) = some (.all σ) := rfl
@[simp] theorem prename_ex (σ : Ty) : prename (Sig := Sig) r (.ex σ) = some (.ex σ) := rfl
@[simp] theorem prename_eq (σ : Ty) : prename (Sig := Sig) r (.eq σ) = some (.eq σ) := rfl
@[simp] theorem prename_constR (ρ : RTy) : prename (Sig := Sig) r (.constR ρ) = some (.constR ρ) := rfl
@[simp] theorem prename_negR (ρ : RTy) : prename (Sig := Sig) r (.negR ρ) = some (.negR ρ) := rfl
@[simp] theorem prename_andR (ρ : RTy) : prename (Sig := Sig) r (.andR ρ) = some (.andR ρ) := rfl
@[simp] theorem prename_orR (ρ : RTy) : prename (Sig := Sig) r (.orR ρ) = some (.orR ρ) := rfl
@[simp] theorem prename_coextR (ρ : RTy) : prename (Sig := Sig) r (.coextR ρ) = some (.coextR ρ) := rfl
@[simp] theorem prename_boxR (ρ : RTy) : prename (Sig := Sig) r (.boxR ρ) = some (.boxR ρ) := rfl
@[simp] theorem prename_inclR (ρ : RTy) : prename (Sig := Sig) r (.inclR ρ) = some (.inclR ρ) := rfl
end

/-- A partial renaming is a section of a renaming: what it sends `u` to, `w` sends back. -/
def PRen.SectionOf {Γ Δ : Ctx} (r : PRen Γ Δ) (w : Ren Δ Γ) : Prop :=
  ∀ σ (u : Var Γ σ) (v : Var Δ σ), r σ u = some v → u = w σ v

theorem PRen.SectionOf.lift {Γ Δ : Ctx} {r : PRen Γ Δ} {w : Ren Δ Γ} (h : r.SectionOf w) (σ : Ty) :
    (r.lift (σ := σ)).SectionOf (Ren.lift w) := by
  intro τ u v hu
  cases u with
  | zero => cases v with
    | zero => rfl
    | succ v => simp [PRen.lift] at hu
  | succ u => cases v with
    | zero => simp [PRen.lift, Option.map_eq_some_iff] at hu
    | succ v =>
      simp only [PRen.lift, Option.map_eq_some_iff] at hu
      obtain ⟨v', hv', e⟩ := hu
      cases e
      exact congrArg Var.succ (h _ _ _ hv')

/-- If a partial renaming is a section of `w`, a term it renames to `t'` is `t'` renamed
by `w`. -/
theorem prename_sound : ∀ {Γ Δ : Ctx} {r : PRen Γ Δ} {w : Ren Δ Γ} (_ : r.SectionOf w)
    {σ : Ty} (t : Term Sig Γ σ) (t' : Term Sig Δ σ), t.prename r = some t' → t = t'.rename w
  | _, _, r, w, h, _, .var v, t', e => by
    simp only [prename_var, Option.map_eq_some_iff] at e
    obtain ⟨v', hv', rfl⟩ := e
    exact congrArg Term.var (h _ _ _ hv')
  | _, _, _, _, _, _, .const _, _, e => by cases e; rfl
  | _, _, r, w, h, _, .app f a, t', e => by
    simp only [prename_app, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨f', hf, a', ha, rfl⟩ := e
    rw [Term.rename_app, ← prename_sound h f f' hf, ← prename_sound h a a' ha]
  | _, _, r, w, h, _, .lam b, t', e => by
    simp only [prename_lam, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨b', hb, rfl⟩ := e
    rw [Term.rename_lam, ← prename_sound (h.lift _) b b' hb]
  | _, _, _, _, _, _, .and, _, e | _, _, _, _, _, _, .or, _, e | _, _, _, _, _, _, .not, _, e
  | _, _, _, _, _, _, .all _, _, e | _, _, _, _, _, _, .ex _, _, e | _, _, _, _, _, _, .eq _, _, e
  | _, _, _, _, _, _, .constR _, _, e | _, _, _, _, _, _, .negR _, _, e | _, _, _, _, _, _, .andR _, _, e
  | _, _, _, _, _, _, .orR _, _, e | _, _, _, _, _, _, .coextR _, _, e | _, _, _, _, _, _, .boxR _, _, e
  | _, _, _, _, _, _, .inclR _, _, e => by
    cases e; rfl

/-- The partial renaming that drops the innermost variable. -/
def PRen.pred {Γ : Ctx} {τ : Ty} : PRen (τ :: Γ) Γ
  | _, .zero => none
  | _, .succ v => some v

theorem PRen.pred_sectionOf {Γ : Ctx} {τ : Ty} :
    (PRen.pred (Γ := Γ) (τ := τ)).SectionOf Ren.shift := by
  intro σ u v hu
  cases u with
  | zero => exact nomatch hu
  | succ u =>
    simp only [PRen.pred, Option.some.injEq] at hu
    rw [hu]; rfl

/-- Remove the innermost variable, if the term does not mention it. -/
def strengthen? {Γ : Ctx} {τ σ : Ty} (t : Term Sig (τ :: Γ) σ) : Option (Term Sig Γ σ) :=
  t.prename PRen.pred

theorem strengthen?_sound {Γ : Ctx} {τ σ : Ty} (t : Term Sig (τ :: Γ) σ) (g : Term Sig Γ σ)
    (h : t.strengthen? = some g) : t = g.weaken (τ := τ) :=
  prename_sound PRen.pred_sectionOf t g h

/-- The η-reduct of `λ. F v`, when `v` is the variable `0` and `F` does not mention it.
Split into two functions so that no pattern nests inside a dependent constructor. -/
def etaVar : ∀ {Γ : Ctx} {σ τ : Ty} {ρ : RTy}, Term Sig (σ :: Γ) (τ ⇒ ρ) → Var (σ :: Γ) τ →
    Option (Term Sig Γ (σ ⇒ ρ))
  | _, _, _, _, f, .zero => f.strengthen?
  | _, _, _, _, _, .succ _ => none

theorem etaVar_sound : ∀ {Γ : Ctx} {σ τ : Ty} {ρ : RTy} (f : Term Sig (σ :: Γ) (τ ⇒ ρ))
    (v : Var (σ :: Γ) τ) (g : Term Sig Γ (σ ⇒ ρ)), etaVar f v = some g →
    Term.lam (.app f (.var v)) ≡ g
  | _, _, _, _, f, .zero, g, h => by
    rw [strengthen?_sound f g h]
    exact Conv.eta g
  | _, _, _, _, _, .succ _, _, h => nomatch h

/-- The η-reduct of `λ. F a`, if `a` is the variable `0` and `F` does not mention it. -/
def etaArg {Γ : Ctx} {σ τ : Ty} {ρ : RTy} (f : Term Sig (σ :: Γ) (τ ⇒ ρ)) :
    Term Sig (σ :: Γ) τ → Option (Term Sig Γ (σ ⇒ ρ))
  | .var v => etaVar f v
  | _ => none

theorem etaArg_sound {Γ : Ctx} {σ τ : Ty} {ρ : RTy} (f : Term Sig (σ :: Γ) (τ ⇒ ρ))
    (a : Term Sig (σ :: Γ) τ) (g : Term Sig Γ (σ ⇒ ρ)) (h : etaArg f a = some g) :
    Term.lam (.app f a) ≡ g := by
  unfold etaArg at h
  split at h
  · exact etaVar_sound f _ g h
  · exact nomatch h

/-- The η-reduct of `λ. b`, if `b` is `F 0` with `F` not mentioning `0`. -/
def etaLam {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig (σ :: Γ) ρ → Option (Term Sig Γ (σ ⇒ ρ))
  | .app f a => etaArg f a
  | _ => none

theorem etaLam_sound {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ)
    (g : Term Sig Γ (σ ⇒ ρ)) (h : etaLam b = some g) : Term.lam b ≡ g := by
  unfold etaLam at h
  split at h
  · exact etaArg_sound _ _ g h
  · exact nomatch h

/-- η-reduce at the root. -/
def etaRed {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig Γ (σ ⇒ ρ) → Term Sig Γ (σ ⇒ ρ)
  | .lam b => (etaLam b).getD (.lam b)
  | t => t

theorem conv_etaRed {Γ : Ctx} {σ : Ty} {ρ : RTy} (t : Term Sig Γ (σ ⇒ ρ)) : t ≡ t.etaRed := by
  unfold etaRed
  split
  · rename_i b
    match h : etaLam b with
    | some g => simp only [Option.getD]; exact etaLam_sound b g h
    | none => simp only [Option.getD]; exact Conv.refl _
  · exact Conv.refl _

/-- One pass of parallel β-reduction, with η-reduction at each abstraction, by
structural recursion: the implementation of `step`.

No δ: the type-subscripted operations are left as they are, even at a constructor type.
The normalizer is evaluated by the kernel, and at a type *variable* an unfolding decided
by matching on the type is stuck, a term the kernel can compare with nothing; the
translator unfolds an operation at a constructor type itself, by `Conv.delta` under
congruences, before it appeals to the normalizer. -/
def stepImpl : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Term Sig Γ σ
  | _, _, .app f a => apply (stepImpl f) (stepImpl a)
  | _, _, .lam b => etaRed (.lam (stepImpl b))
  | _, _, t => t

/-- One pass of parallel β-reduction, with η-reduction at each abstraction. Through
`Term.rec`, as `Term.rename` is, and for the same reason. -/
@[implemented_by stepImpl]
def step : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Term Sig Γ σ :=
  fun t =>
    Term.rec (motive := fun Γ σ _ => Term Sig Γ σ)
      (var := fun v => Term.var v) (const := fun c => Term.const c)
      (app := fun _ _ f a => apply f a) (lam := fun _ b => etaRed (Term.lam b))
      (and := Term.and) (or := Term.or) (not := Term.not)
      (all := fun σ => Term.all σ) (ex := fun σ => Term.ex σ) (eq := fun σ => Term.eq σ)
      (constR := fun ρ => Term.constR ρ) (negR := fun ρ => Term.negR ρ)
      (andR := fun ρ => Term.andR ρ) (orR := fun ρ => Term.orR ρ)
      (coextR := fun ρ => Term.coextR ρ) (boxR := fun ρ => Term.boxR ρ)
      (inclR := fun ρ => Term.inclR ρ) t

section
variable {Γ : Ctx}
@[simp] theorem step_var {σ : Ty} (v : Var Γ σ) : step (Sig := Sig) (.var v) = .var v := rfl
@[simp] theorem step_const (c : Sig.Const) : step (Γ := Γ) (.const c) = .const c := rfl
@[simp] theorem step_app {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    step (.app f a) = apply (step f) (step a) := rfl
@[simp] theorem step_lam {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    step (.lam b) = etaRed (.lam (step b)) := rfl
@[simp] theorem step_and : step (Sig := Sig) (Γ := Γ) .and = .and := rfl
@[simp] theorem step_or : step (Sig := Sig) (Γ := Γ) .or = .or := rfl
@[simp] theorem step_not : step (Sig := Sig) (Γ := Γ) .not = .not := rfl
@[simp] theorem step_all (σ : Ty) : step (Sig := Sig) (Γ := Γ) (.all σ) = .all σ := rfl
@[simp] theorem step_ex (σ : Ty) : step (Sig := Sig) (Γ := Γ) (.ex σ) = .ex σ := rfl
@[simp] theorem step_eq (σ : Ty) : step (Sig := Sig) (Γ := Γ) (.eq σ) = .eq σ := rfl
@[simp] theorem step_constR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.constR ρ) = .constR ρ := rfl
@[simp] theorem step_negR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.negR ρ) = .negR ρ := rfl
@[simp] theorem step_andR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.andR ρ) = .andR ρ := rfl
@[simp] theorem step_orR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.orR ρ) = .orR ρ := rfl
@[simp] theorem step_coextR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.coextR ρ) = .coextR ρ := rfl
@[simp] theorem step_boxR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.boxR ρ) = .boxR ρ := rfl
@[simp] theorem step_inclR (ρ : RTy) : step (Sig := Sig) (Γ := Γ) (.inclR ρ) = .inclR ρ := rfl
end

theorem conv_step : ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t ≡ step t
  | _, _, .app f a =>
    Conv.trans (Conv.app_congr (conv_step f) (conv_step a)) (conv_apply _ _)
  | _, _, .lam b => Conv.trans (Conv.lam_congr (conv_step b)) (conv_etaRed _)
  | _, _, .var _ | _, _, .const _ | _, _, .and | _, _, .or | _, _, .not
  | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => Conv.refl _
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .inclR _ => Conv.refl _

/-- `n` passes of parallel β-reduction. Through `Nat.rec`, for the kernel. -/
def nf {Γ : Ctx} {σ : Ty} (n : Nat) (t : Term Sig Γ σ) : Term Sig Γ σ :=
  Nat.rec (motive := fun _ => Term Sig Γ σ → Term Sig Γ σ) (fun t => t) (fun _ ih t => ih (step t)) n t

@[simp] theorem nf_zero {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ) : nf 0 t = t := rfl
@[simp] theorem nf_succ {Γ : Ctx} {σ : Ty} (n : Nat) (t : Term Sig Γ σ) : nf (n + 1) t = nf n (step t) := rfl

theorem conv_nf {Γ : Ctx} {σ : Ty} : ∀ (n : Nat) (t : Term Sig Γ σ), t ≡ nf n t
  | 0, _ => Conv.refl _
  | n + 1, t => Conv.trans (conv_step t) (conv_nf n (step t))

end Term

/-- Two terms with the same normal form are convertible. The hypothesis is decided by
evaluation: `Conv.of_nf n a b rfl`. -/
theorem Conv.of_nf {Γ : Ctx} {σ : Ty} (n : Nat) (a b : Term Sig Γ σ) (h : Term.nf n a = Term.nf n b) :
    a ≡ b :=
  Conv.trans (Term.conv_nf n a) (h ▸ Conv.symm (Term.conv_nf n b))

/-- One-sided forms, for when one term is already normal: the kernel then evaluates the
normalizer on one side only. -/
theorem Conv.of_nf_left {Γ : Ctx} {σ : Ty} (n : Nat) (a b : Term Sig Γ σ) (h : Term.nf n a = b) :
    a ≡ b :=
  h ▸ Term.conv_nf n a

theorem Conv.of_nf_right {Γ : Ctx} {σ : Ty} (n : Nat) (a b : Term Sig Γ σ) (h : a = Term.nf n b) :
    a ≡ b :=
  Conv.symm (h ▸ Term.conv_nf n b)

end Classicism.Meta
