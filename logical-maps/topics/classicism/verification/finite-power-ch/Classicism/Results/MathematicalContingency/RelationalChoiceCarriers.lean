import Classicism.Results.MathematicalContingency.Definitions
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem

/-! Finite-Power CH Strategy: current carrier-relative selection.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
Relational Choice is an explicit object-language hypothesis, never Lean choice.
-/
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

theorem relationalChoice_on_carriers (A : α → Prop) (B : β → Prop)
    (R : α → β → Prop) (fallback : β) (choice : P.RelationalChoice α β)
    (serial : ∀ a, A a → ∃ b, B b ∧ R a b) :
    ∃ F, Maps F A B ∧ ∀ a b, F a b → R a b := by
  let U : α → β → Prop := fun a b =>
    (A a ∧ B b ∧ R a b) ∨ (¬ A a ∧ b = fallback)
  have total : P.Serial U := by
    intro a
    obtain ha | ha := em (A a)
    · obtain ⟨b,hb,hr⟩ := serial a ha
      exact ⟨b,Or.inl ⟨ha,hb,hr⟩⟩
    · exact ⟨fallback,Or.inr ⟨ha,rfl⟩⟩
  obtain ⟨S,hs,sub⟩ := choice U total
  let F : α → β → Prop := fun a b => A a ∧ S a b
  have data : ∀ a b, F a b → B b ∧ R a b := by
    intro a b h
    exact (sub a b h.2).elim (fun k => k.2) (fun k => (k.1 h.1).elim)
  refine ⟨F,⟨fun a b h => ⟨h.1,(data a b h).1⟩,?_,?_⟩,
    fun a b h => (data a b h).2⟩
  · intro a ha
    obtain ⟨b,hb,_⟩ := hs a
    exact ⟨b,(data a b ⟨ha,hb⟩).1,ha,hb⟩
  · intro a b c hb hc
    obtain ⟨d,_,unique⟩ := hs a
    exact (unique b hb.2).symm.trans (unique c hc.2)

/-- Actual tuple codes; equality is intensional, so evaluation gives injectivity. -/
def ChoicePairTag (a : α) (b : β) : α → β → Prop :=
  fun x y => x = a ∧ y = b

theorem choicePairTag_injective (a c : α) (b d : β)
    (h : ChoicePairTag a b = ChoicePairTag c d) : a = c ∧ b = d :=
  Eq.mp (congrArg (fun T => T a b) h) ⟨rfl,rfl⟩

def ChoicePairCarrier (A : α → Prop) (B : β → Prop) (t : α → β → Prop) : Prop :=
  ∃ a b, A a ∧ B b ∧ t = ChoicePairTag a b

def ChoicePairRelation (A : α → Prop) (B : β → Prop) (R : α → β → γ → Prop)
    (t : α → β → Prop) (d : γ) : Prop :=
  ∃ a b, A a ∧ B b ∧ t = ChoicePairTag a b ∧ R a b d

theorem relationalChoice_on_pairs (A : α → Prop) (B : β → Prop)
    (D : γ → Prop) (R : α → β → γ → Prop) (fallback : γ)
    (choice : P.RelationalChoice (α → β → Prop) γ)
    (serial : ∀ a b, A a → B b → ∃ d, D d ∧ R a b d) :
    ∃ T : α → β → γ → Prop,
      (∀ a b d, T a b d → A a ∧ B b ∧ D d ∧ R a b d) ∧
      (∀ a b, A a → B b → ∃ d, T a b d) ∧
      (∀ a b d f, T a b d → T a b f → d = f) := by
  have total : ∀ t, ChoicePairCarrier A B t → ∃ d, D d ∧ ChoicePairRelation A B R t d := by
    intro t ⟨a,b,ha,hb,ht⟩
    obtain ⟨d,hd,hr⟩ := serial a b ha hb
    exact ⟨d,hd,a,b,ha,hb,ht,hr⟩
  obtain ⟨F,hF,hsub⟩ := relationalChoice_on_carriers (ChoicePairCarrier A B) D
    (ChoicePairRelation A B R) fallback choice total
  let T : α → β → γ → Prop := fun a b d => A a ∧ B b ∧ F (ChoicePairTag a b) d
  refine ⟨T,?_,?_,?_⟩
  · intro a b d ht
    obtain ⟨x,y,hx,hy,he,hr⟩ := hsub _ d ht.2.2
    obtain ⟨ex,ey⟩ := choicePairTag_injective a x b y he
    subst x
    subst y
    exact ⟨ht.1,ht.2.1,(hF.1 _ d ht.2.2).2,hr⟩
  · intro a b ha hb
    obtain ⟨d,_,hd⟩ := hF.2.1 (ChoicePairTag a b) ⟨a,b,ha,hb,rfl⟩
    exact ⟨d,ha,hb,hd⟩
  · intro a b d f hd hf
    exact hF.2.2 _ d f hd.2.2 hf.2.2

#classicism_check relationalChoice_on_carriers choicePairTag_injective relationalChoice_on_pairs
#classicism_types relationalChoice_on_carriers choicePairTag_injective relationalChoice_on_pairs
end Classicism.MathematicalContingency
