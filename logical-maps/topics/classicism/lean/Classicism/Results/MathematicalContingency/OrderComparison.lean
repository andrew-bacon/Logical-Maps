import Classicism.Results.MathematicalContingency.OrdinalStructurality
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
theorem initial_embeddings_agree (A : σ → Prop) (B : τ → Prop)
    (R : σ → σ → Prop) (S : τ → τ → Prop) (F G : σ → τ → Prop)
    (hw : WellOrderOn A R) (hs : StrictOrderOn B S)
    (hf : InitialEmbedding F A R B S) (hg : InitialEmbedding G A R B S) :
    ∀ x, A x → ∀ u v, F x u → G x v → u = v := by
  apply wellOrder_induction A R hw (fun x => ∀ u v, F x u → G x v → u = v)
  intro x hx ih u v hxu hxv
  obtain he | huv | hvu := hs.2.2.2 u v (hf.1.1.1.1 x u hxu).2 (hg.1.1.1.1 x v hxv).2
  · exact he
  · obtain ⟨w,hwx,hwu⟩ := hg.2 x v u hxv (hf.1.1.1.1 x u hxu).2 huv
    have hwA := (hg.1.1.1.1 w u hwu).1
    obtain ⟨z,hz,hwz⟩ := hf.1.1.1.2.1 w hwA
    have he := ih w hwA hwx z u hwz hwu
    have hwu' : F w u := he ▸ hwz
    have hwEq := hf.1.1.2 w x u hwu' hxu
    exact (hw.1.2.1 x hx (Eq.mp (congrArg (fun q => R q x) hwEq) hwx)).elim
  · obtain ⟨w,hwx,hwv⟩ := hf.2 x u v hxu (hg.1.1.1.1 x v hxv).2 hvu
    have hwA := (hf.1.1.1.1 w v hwv).1
    obtain ⟨z,hz,hwz⟩ := hg.1.1.1.2.1 w hwA
    have he := ih w hwA hwx v z hwv hwz
    have hwv' : G w v := he.symm ▸ hwz
    have hwEq := hg.1.1.2 w x v hwv' hxv
    exact (hw.1.2.1 x hx (Eq.mp (congrArg (fun q => R q x) hwEq) hwx)).elim

theorem initial_embeddings_coext (A : σ → Prop) (B : τ → Prop)
    (R : σ → σ → Prop) (S : τ → τ → Prop) (F G : σ → τ → Prop)
    (hw : WellOrderOn A R) (hs : StrictOrderOn B S)
    (hf : InitialEmbedding F A R B S) (hg : InitialEmbedding G A R B S) :
    ∀ x y, F x y ↔ G x y := by
  intro x y
  constructor
  · intro hxy
    have hx := (hf.1.1.1.1 x y hxy).1
    obtain ⟨z,hz,hxz⟩ := hg.1.1.1.2.1 x hx
    exact (initial_embeddings_agree A B R S F G hw hs hf hg x hx y z hxy hxz).symm ▸ hxz
  · intro hxy
    have hx := (hg.1.1.1.1 x y hxy).1
    obtain ⟨z,hz,hxz⟩ := hf.1.1.1.2.1 x hx
    exact initial_embeddings_agree A B R S F G hw hs hf hg x hx z y hxz hxy ▸ hxz
#classicism_check initial_embeddings_agree initial_embeddings_coext
#classicism_types initial_embeddings_agree initial_embeddings_coext
end Classicism.MathematicalContingency
