import Classicism.Results.MathematicalContingency.CarrierTheory
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
def CBPart (A : σ → Prop) (F : σ → τ → Prop) (G : τ → σ → Prop) (a : σ) : Prop :=
  ∀ Z : σ → Prop, (∀ x, A x → (¬ ∃ y, G y x) → Z x) →
    (∀ x y z, Z x → F x y → G y z → Z z) → Z a

theorem cb_base (A : σ → Prop) (F : σ → τ → Prop) (G : τ → σ → Prop)
    (a : σ) (ha : A a) (hn : ¬ ∃ y, G y a) : CBPart A F G a := fun _ hb _ => hb a ha hn
theorem cb_step (A : σ → Prop) (F : σ → τ → Prop) (G : τ → σ → Prop)
    (a : σ) (b : τ) (c : σ) (h : CBPart A F G a) (hf : F a b) (hg : G b c) :
    CBPart A F G c := fun Z hb hs => hs a b c (h Z hb hs) hf hg
theorem cb_cases (A : σ → Prop) (F : σ → τ → Prop) (G : τ → σ → Prop)
    (a : σ) (h : CBPart A F G a) :
    (A a ∧ ¬ ∃ b, G b a) ∨ ∃ x b, CBPart A F G x ∧ F x b ∧ G b a :=
  (h (fun z => CBPart A F G z ∧ ((A z ∧ ¬ ∃ b, G b z) ∨ ∃ x b, CBPart A F G x ∧ F x b ∧ G b z))
    (fun x hx hn => ⟨cb_base A F G x hx hn,Or.inl ⟨hx,hn⟩⟩)
    (fun x y z hx hf hg => ⟨cb_step A F G x y z hx.1 hf hg,Or.inr ⟨x,y,hx.1,hf,hg⟩⟩)).2

theorem cb_subset (A : σ → Prop) (B : τ → Prop) (F : σ → τ → Prop) (G : τ → σ → Prop)
    (hg : Maps G B A) (a : σ) (h : CBPart A F G a) : A a :=
  h A (fun _ ha _ => ha) (fun _ y z _ _ hyz => (hg.1 y z hyz).2)

theorem cantor_bernstein_relations (A : σ → Prop) (B : τ → Prop)
    (F : σ → τ → Prop) (G : τ → σ → Prop) (hf : Injects F A B) (hg : Injects G B A) :
    Equinumerous A B := by
  let H : σ → τ → Prop := fun a b => (CBPart A F G a ∧ F a b) ∨ (¬ CBPart A F G a ∧ G b a)
  have back : ∀ a, A a → ¬ CBPart A F G a → ∃ b, G b a := by
    intro a ha hn
    exact (em (∃ b, G b a)).elim (fun h => h) (fun h => (hn (cb_base A F G a ha h)).elim)
  have pred : ∀ a b, CBPart A F G a → G b a → ∃ x, CBPart A F G x ∧ F x b := by
    intro a b ha hba
    obtain h0 | ⟨x,c,hx,hxc,hca⟩ := cb_cases A F G a ha
    · exact (h0.2 ⟨b,hba⟩).elim
    have he := hg.2 c b a hca hba
    exact ⟨x,hx,he ▸ hxc⟩
  have hm : Maps H A B := by
    refine ⟨?_,?_,?_⟩
    · intro a b h
      exact h.elim (fun h => hf.1.1 a b h.2) (fun h => ⟨(hg.1.1 b a h.2).2,(hg.1.1 b a h.2).1⟩)
    · intro a ha
      refine (em (CBPart A F G a)).elim ?_ ?_
      · intro h; obtain ⟨b,hb,hab⟩ := hf.1.2.1 a ha
        exact ⟨b,hb,Or.inl ⟨h,hab⟩⟩
      · intro h; obtain ⟨b,hba⟩ := back a ha h
        exact ⟨b,(hg.1.1 b a hba).1,Or.inr ⟨h,hba⟩⟩
    · intro a b c hb hc
      exact hb.elim
        (fun hb => hc.elim (fun hc => hf.1.2.2 a b c hb.2 hc.2) (fun hc => (hc.1 hb.1).elim))
        (fun hb => hc.elim (fun hc => (hb.1 hc.1).elim) (fun hc => hg.2 b c a hb.2 hc.2))
  refine ⟨H,⟨⟨hm,?_⟩,hm,?_⟩⟩
  · intro a c b ha hc
    exact ha.elim
      (fun ha => hc.elim (fun hc => hf.2 a c b ha.2 hc.2)
        (fun hc => (hc.1 (cb_step A F G a b c ha.1 ha.2 hc.2)).elim))
      (fun ha => hc.elim (fun hc => (ha.1 (cb_step A F G c b a hc.1 hc.2 ha.2)).elim)
        (fun hc => hg.1.2.2 b a c ha.2 hc.2))
  · intro b hb
    obtain ⟨a,ha,hba⟩ := hg.1.2.1 b hb
    refine (em (CBPart A F G a)).elim ?_ ?_
    · intro h
      obtain ⟨x,hx,hxb⟩ := pred a b h hba
      exact ⟨x,(hf.1.1 x b hxb).1,Or.inl ⟨hx,hxb⟩⟩
    · intro h; exact ⟨a,ha,Or.inr ⟨h,hba⟩⟩

theorem cantor_bernstein (A : σ → Prop) (B : τ → Prop)
    (h : Embeds A B) (k : Embeds B A) : Equinumerous A B :=
  h.elim fun F hf => k.elim fun G hg => cantor_bernstein_relations A B F G hf hg
#classicism_check cb_base cb_step cb_cases cb_subset cantor_bernstein_relations cantor_bernstein
#classicism_types cb_base cb_step cb_cases cb_subset cantor_bernstein_relations cantor_bernstein
end Classicism.MathematicalContingency
