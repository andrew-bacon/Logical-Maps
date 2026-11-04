import Classicism.Background.ChurchSequences
import Classicism.Background.Relations
import Classicism.Principles.Recursion

/-!
Least-graph recursion proofs, following Andrew Bacon's 2023 construction.
Formalization by Codex (OpenAI), prompted by Andrew Bacon, 4 November 2026.
No recursion principle is used as a premise.
-/
namespace Classicism.Church

section graphs
variable {α σ τ : Type} [Rel α] [Ty σ] [Rel τ]

theorem numGraph_zero (a : τ) (g : τ → τ) : NumGraph a g (zero α) a :=
  fun _ h ↦ h.1

theorem numGraph_suc (a : τ) (g : τ → τ) (n : Num α) (x : τ)
    (h : NumGraph a g n x) : NumGraph a g (suc n) (g x) :=
  fun R hR ↦ hR.2 n x (h R hR)

theorem numGraph_support (a : τ) (g : τ → τ) (n : Num α) (x : τ)
    (h : NumGraph a g n x) : Nat n :=
  h (fun n _ ↦ Nat n) ⟨nat_zero, fun _ _ hn ↦ nat_suc hn⟩

theorem numGraph_total (a : τ) (g : τ → τ) (n : Num α) (hn : Nat n) :
    ∃ x, NumGraph a g n x :=
  hn (fun n ↦ ∃ x, NumGraph a g n x)
    ⟨⟨a, numGraph_zero a g⟩, fun m ⟨y, hy⟩ ↦ ⟨g y, numGraph_suc a g m y hy⟩⟩

theorem numGraph_unfold (a : τ) (g : τ → τ) (n : Num α) (x : τ)
    (h : NumGraph a g n x) :
    (n = zero α ∧ x = a) ∨ ∃ m y, n = suc m ∧ NumGraph a g m y ∧ x = g y := by
  apply h (fun n x ↦ (n = zero α ∧ x = a) ∨
    ∃ m y, n = suc m ∧ NumGraph a g m y ∧ x = g y)
  constructor
  · exact Or.inl ⟨rfl, rfl⟩
  · intro m y hy
    have hs : NumGraph a g m y := by
      rcases hy with ⟨rfl, rfl⟩ | ⟨k, z, rfl, hz, rfl⟩
      · exact numGraph_zero _ g
      · exact numGraph_suc a g k z hz
    exact Or.inr ⟨m, y, rfl, hs, rfl⟩

theorem numGraph_at_zero (a : τ) (g : τ → τ) (hI : Infinity α) (x : τ)
    (h : NumGraph a g (zero α) x) : x = a := by
  rcases numGraph_unfold a g (zero α) x h with h | ⟨m, y, he, hy, _⟩
  · exact h.2
  · exact False.elim (hI.1 m (numGraph_support a g m y hy) he.symm)

theorem numGraph_at_suc (a : τ) (g : τ → τ) (hI : Infinity α)
    (n : Num α) (hn : Nat n) (x : τ) (h : NumGraph a g (suc n) x) :
    ∃ y, NumGraph a g n y ∧ x = g y := by
  rcases numGraph_unfold a g (suc n) x h with h | ⟨m, y, he, hy, hx⟩
  · exact False.elim (hI.1 n hn h.1)
  · have e := hI.2 n m hn (numGraph_support a g m y hy) he
    exact ⟨y, e.symm ▸ hy, hx⟩

theorem numGraph_functional (a : τ) (g : τ → τ) (hI : Infinity α) :
    ∀ (n : Num α) x y, NumGraph a g n x → NumGraph a g n y → x = y := by
  intro n x y hx hy
  have h := (numGraph_support a g n x hx)
    (fun n ↦ Nat n ∧ ∀ x y, NumGraph a g n x → NumGraph a g n y → x = y)
    ⟨⟨nat_zero, fun x y hx hy ↦ (numGraph_at_zero a g hI x hx).trans
      (numGraph_at_zero a g hI y hy).symm⟩,
      fun m ih ↦ ⟨nat_suc ih.1, by
        intro x y hx hy
        obtain ⟨u, hu, ex⟩ := numGraph_at_suc a g hI m ih.1 x hx
        obtain ⟨v, hv, ey⟩ := numGraph_at_suc a g hI m ih.1 y hy
        exact ex.trans ((congrArg g (ih.2 u v hu hv)).trans ey.symm)⟩⟩
  exact h.2 x y hx hy

theorem numGraph_persistent (a : τ) (g : τ → τ) (n : Num α) (x : τ)
    (h : NumGraph a g n x) : □ (NumGraph a g n x) :=
  h (fun n x ↦ □ (NumGraph a g n x))
    ⟨nec% (numGraph_zero a g), fun m y hy ↦
      modal_K _ _ (nec% (numGraph_suc a g m y)) hy⟩

theorem seqGraph_nil (a : τ) (g : σ → τ → τ) : SeqGraph a g (nil α σ) a :=
  fun _ h ↦ h.1

theorem seqGraph_cons (a : τ) (g : σ → τ → τ) (b : σ) (s : Seq α σ) (x : τ)
    (h : SeqGraph a g s x) : SeqGraph a g (cons b s) (g b x) :=
  fun R hR ↦ hR.2 b s x (h R hR)

theorem seqGraph_support (a : τ) (g : σ → τ → τ) (s : Seq α σ) (x : τ)
    (h : SeqGraph a g s x) : Finite s :=
  h (fun s _ ↦ Finite s) ⟨finite_nil, fun b _ _ hs ↦ finite_cons b hs⟩

theorem seqGraph_total (a : τ) (g : σ → τ → τ) (s : Seq α σ) (hs : Finite s) :
    ∃ x, SeqGraph a g s x :=
  hs (fun s ↦ ∃ x, SeqGraph a g s x)
    ⟨⟨a, seqGraph_nil a g⟩, fun b r ⟨y, hy⟩ ↦ ⟨g b y, seqGraph_cons a g b r y hy⟩⟩

theorem seqGraph_unfold (a : τ) (g : σ → τ → τ) (s : Seq α σ) (x : τ)
    (h : SeqGraph a g s x) :
    (s = nil α σ ∧ x = a) ∨ ∃ b r y, s = cons b r ∧ SeqGraph a g r y ∧ x = g b y := by
  apply h (fun s x ↦ (s = nil α σ ∧ x = a) ∨
    ∃ b r y, s = cons b r ∧ SeqGraph a g r y ∧ x = g b y)
  constructor
  · exact Or.inl ⟨rfl, rfl⟩
  · intro b r y hy
    have hs : SeqGraph a g r y := by
      rcases hy with ⟨rfl, rfl⟩ | ⟨c, v, z, rfl, hz, rfl⟩
      · exact seqGraph_nil _ g
      · exact seqGraph_cons a g c v z hz
    exact Or.inr ⟨b, r, y, rfl, hs, rfl⟩

theorem seqGraph_at_nil (a : τ) (g : σ → τ → τ) (hI : Infinity α) (x : τ)
    (h : SeqGraph a g (nil α σ) x) : x = a := by
  rcases seqGraph_unfold a g (nil α σ) x h with h | ⟨b, r, y, he, _, _⟩
  · exact h.2
  · exact False.elim (cons_ne_nil hI b r he.symm)

theorem seqGraph_at_cons (a : τ) (g : σ → τ → τ) (hI : Infinity α)
    (b : σ) (s : Seq α σ) (hs : Finite s) (x : τ)
    (h : SeqGraph a g (cons b s) x) : ∃ y, SeqGraph a g s y ∧ x = g b y := by
  rcases seqGraph_unfold a g (cons b s) x h with h | ⟨c, r, y, he, hy, hx⟩
  · exact False.elim (cons_ne_nil hI b s h.1)
  · have e := cons_injective hI b c s r hs (seqGraph_support a g r y hy) he
    exact ⟨y, e.2.symm ▸ hy, e.1.symm ▸ hx⟩

theorem seqGraph_functional (a : τ) (g : σ → τ → τ) (hI : Infinity α) :
    ∀ (s : Seq α σ) x y, SeqGraph a g s x → SeqGraph a g s y → x = y := by
  intro s x y hx hy
  have h := (seqGraph_support a g s x hx)
    (fun s ↦ Finite s ∧ ∀ x y, SeqGraph a g s x → SeqGraph a g s y → x = y)
    ⟨⟨finite_nil, fun x y hx hy ↦ (seqGraph_at_nil a g hI x hx).trans
      (seqGraph_at_nil a g hI y hy).symm⟩,
      fun b r ih ↦ ⟨finite_cons b ih.1, by
        intro x y hx hy
        obtain ⟨u, hu, ex⟩ := seqGraph_at_cons a g hI b r ih.1 x hx
        obtain ⟨v, hv, ey⟩ := seqGraph_at_cons a g hI b r ih.1 y hy
        exact ex.trans ((congrArg (g b) (ih.2 u v hu hv)).trans ey.symm)⟩⟩
  exact h.2 x y hx hy

theorem seqGraph_persistent (a : τ) (g : σ → τ → τ) (s : Seq α σ) (x : τ)
    (h : SeqGraph a g s x) : □ (SeqGraph a g s x) :=
  h (fun s x ↦ □ (SeqGraph a g s x))
    ⟨nec% (seqGraph_nil a g), fun b r y hy ↦
      modal_K _ _ (nec% (seqGraph_cons a g b r y)) hy⟩
end graphs

/-- Localize functionality to a graph value before necessitating the implication. -/
theorem graph_unique_at {ι δ : Type} [Ty ι] [Ty δ]
    (R : ι → (δ → Prop) → Prop) (s : ι) (x : δ → Prop) :
    (∀ r u v, R r u → R r v → u = v) → R s x → (R s x ∧ ∀ y, R s y → x = y) :=
  fun hu hx ↦ ⟨hx, fun y hy ↦ hu s x y hx hy⟩

theorem graph_value {ι δ : Type} [Ty ι] [Ty δ]
    (R : ι → (δ → Prop) → Prop) (s : ι) (x : δ → Prop)
    (hu : □ (∀ r u v, R r u → R r v → u = v)) (hx : □ (R s x)) :
    (fun z ↦ ∀ y, R s y → y z) = x :=
  (mp_value R s x (modal_K _ _
    (modal_K _ _ (nec% (graph_unique_at R s x)) hu) hx)).symm

theorem num_recursion_unary {δ α : Type} [Ty δ] [Rel α] :
    P.NecChurchNumeralInfinity α → P.ChurchNumeralFunctionalRecursion α (δ → Prop) := by
  intro hI a g
  have hu := modal_K _ _ (nec% (numGraph_functional (α := α) a g)) hI
  refine ⟨fun n z ↦ ∀ y, NumGraph a g n y → y z, ?_, ?_⟩
  · exact graph_value (NumGraph a g) (zero α) a hu
      (numGraph_persistent a g (zero α) a (numGraph_zero a g))
  · intro n hn
    obtain ⟨x, hx⟩ := numGraph_total a g n hn
    have ex := graph_value (NumGraph a g) n x hu (numGraph_persistent a g n x hx)
    have es := graph_value (NumGraph a g) (suc n) (g x) hu
      (numGraph_persistent a g (suc n) (g x) (numGraph_suc a g n x hx))
    exact es.trans (congrArg g ex.symm)

theorem seq_recursion_unary {δ α σ : Type} [Ty δ] [Rel α] [Ty σ] :
    P.NecChurchNumeralInfinity α → P.SequenceFunctionalRecursion α σ (δ → Prop) := by
  intro hI a g
  have hu := modal_K _ _ (nec% (seqGraph_functional (α := α) a g)) hI
  refine ⟨fun s z ↦ ∀ y, SeqGraph a g s y → y z, ?_, ?_⟩
  · exact graph_value (SeqGraph a g) (nil α σ) a hu
      (seqGraph_persistent a g (nil α σ) a (seqGraph_nil a g))
  · intro b s hs
    obtain ⟨x, hx⟩ := seqGraph_total a g s hs
    have ex := graph_value (SeqGraph a g) s x hu (seqGraph_persistent a g s x hx)
    have es := graph_value (SeqGraph a g) (cons b s) (g b x) hu
      (seqGraph_persistent a g (cons b s) (g b x) (seqGraph_cons a g b s x hx))
    exact es.trans (congrArg (g b) ex.symm)
end Classicism.Church
