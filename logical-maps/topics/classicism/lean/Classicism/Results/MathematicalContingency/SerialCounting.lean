import Classicism.Results.MathematicalContingency.RelationalProduct

/-! Counting a serial relation with uniformly coded fibres, without Choice.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β γ ν : Type} [Ty α] [Ty β] [Ty γ] [Ty ν]

def LeastRelated (A : α → Prop) (B : β → Prop) (L : β → β → Prop)
    (J : α → β → Prop) (a : α) (b : β) : Prop :=
  A a ∧ B b ∧ J a b ∧ ∀ c, B c → J a c → ¬ L c b

/-- A single ternary relation supplies all the fibre injections. -/
def UniformFibreCodes (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (J : α → β → Prop) (T : β → α → γ → Prop) : Prop :=
  ∀ b, B b → Injects (T b) (fun a => A a ∧ J a b) K

def SerialCode (A : α → Prop) (B : β → Prop) (L : β → β → Prop)
    (J : α → β → Prop) (T : β → α → γ → Prop) (a : α) (b : β) (n : γ) : Prop :=
  LeastRelated A B L J a b ∧ T b a n

theorem leastRelated_exists (A : α → Prop) (B : β → Prop) (L : β → β → Prop)
    (J : α → β → Prop) (hw : WellOrderOn B L)
    (serial : ∀ a, A a → ∃ b, B b ∧ J a b) (a : α) (ha : A a) :
    ∃ b, LeastRelated A B L J a b := by
  obtain ⟨b,hb,hm⟩ := hw.2 (fun b => B b ∧ J a b) (fun _ h => h.1) (serial a ha)
  exact ⟨b,ha,hb.1,hb.2,fun c hc hj => hm c ⟨hc,hj⟩⟩

theorem leastRelated_unique (A : α → Prop) (B : β → Prop) (L : β → β → Prop)
    (J : α → β → Prop) (hw : WellOrderOn B L) (a : α) (b c : β)
    (hb : LeastRelated A B L J a b) (hc : LeastRelated A B L J a c) : b = c := by
  obtain e | h | h := hw.1.2.2.2 b c hb.2.1 hc.2.1
  · exact e
  · exact (hc.2.2.2 b hb.2.1 hb.2.2.1 h).elim
  · exact (hb.2.2.2 c hc.2.1 hc.2.2.1 h).elim

theorem serialCode_total (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (L : β → β → Prop) (J : α → β → Prop) (T : β → α → γ → Prop)
    (hw : WellOrderOn B L) (serial : ∀ a, A a → ∃ b, B b ∧ J a b)
    (codes : UniformFibreCodes A B K J T) (a : α) (ha : A a) :
    ∃ b n, B b ∧ K n ∧ SerialCode A B L J T a b n := by
  obtain ⟨b,hb⟩ := leastRelated_exists A B L J hw serial a ha
  obtain ⟨n,hn,ht⟩ := (codes b hb.2.1).1.2.1 a ⟨ha,hb.2.2.1⟩
  exact ⟨b,n,hb.2.1,hn,hb,ht⟩

theorem serialCode_functional (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (L : β → β → Prop) (J : α → β → Prop) (T : β → α → γ → Prop)
    (hw : WellOrderOn B L) (codes : UniformFibreCodes A B K J T)
    (a : α) (b c : β) (n m : γ)
    (h : SerialCode A B L J T a b n) (k : SerialCode A B L J T a c m) :
    b = c ∧ n = m := by
  have e := leastRelated_unique A B L J hw a b c h.1 k.1
  subst c
  exact ⟨rfl,(codes b h.1.2.1).1.2.2 a n m h.2 k.2⟩

theorem serialCode_injective (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (L : β → β → Prop) (J : α → β → Prop) (T : β → α → γ → Prop)
    (codes : UniformFibreCodes A B K J T) (a a' : α) (b : β) (n : γ)
    (h : SerialCode A B L J T a b n) (k : SerialCode A B L J T a' b n) : a = a' :=
  (codes b h.1.2.1).2 a a' n h.2 k.2

theorem serial_embeds_product (A : α → Prop) (B : β → Prop) (K : γ → Prop)
    (L : β → β → Prop) (J : α → β → Prop) (T : β → α → γ → Prop)
    (hw : WellOrderOn B L) (serial : ∀ a, A a → ∃ b, B b ∧ J a b)
    (codes : UniformFibreCodes A B K J T)
    (rc : P.RigidComprehension (β → γ → Prop)) : Embeds A (RelProduct B K) := by
  refine ⟨fun a P => ∃ b n, SerialCode A B L J T a b n ∧ ProductPairAt B K P b n,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro a P h
    obtain ⟨b,n,hc,hp⟩ := h
    exact ⟨hc.1.1,b,n,hp⟩
  · intro a ha
    obtain ⟨b,n,hb,hn,hc⟩ := serialCode_total A B K L J T hw serial codes a ha
    obtain ⟨P,hP⟩ := productPairAt_exists B K rc b n hb hn
    exact ⟨P,⟨b,n,hP⟩,b,n,hc,hP⟩
  · intro a P Q hp hq
    obtain ⟨b,n,hc,hP⟩ := hp
    obtain ⟨c,m,hc',hQ⟩ := hq
    obtain ⟨e,f⟩ := serialCode_functional A B K L J T hw codes a b c n m hc hc'
    subst c; subst m
    exact productPairAt_unique B K P Q b n hP hQ
  · intro a a' P hp hq
    obtain ⟨b,n,hc,hP⟩ := hp
    obtain ⟨c,m,hc',hP'⟩ := hq
    obtain ⟨e,f⟩ := productPairAt_coordinates B K P b c n m hP hP'
    subst c; subst m
    exact serialCode_injective A B K L J T codes a a' b n hc hc'

/-- The paper's countable-fibre instance; no Peano or modal N hypothesis is needed here. -/
theorem serial_countable_fibres (A : α → Prop) (B : β → Prop)
    (L : β → β → Prop) (J : α → β → Prop)
    (T : β → α → ((ν → Prop) → Prop) → Prop)
    (hw : WellOrderOn B L) (serial : ∀ a, A a → ∃ b, B b ∧ J a b)
    (codes : UniformFibreCodes A B (@LowerNat ν _) J T)
    (rc : P.RigidComprehension (β → ((ν → Prop) → Prop) → Prop)) :
    Embeds A (RelProduct B (@LowerNat ν _)) :=
  serial_embeds_product A B LowerNat L J T hw serial codes rc

#classicism_check leastRelated_exists leastRelated_unique serialCode_total serialCode_functional
  serialCode_injective serial_embeds_product serial_countable_fibres
#classicism_types leastRelated_exists leastRelated_unique serialCode_total serialCode_functional
  serialCode_injective serial_embeds_product serial_countable_fibres
end Classicism.MathematicalContingency
