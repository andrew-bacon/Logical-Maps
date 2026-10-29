import Classicism.Results.MathematicalContingency.OrderComparison
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
def DownClosed (A : σ → Prop) (R : σ → σ → Prop) (D : σ → Prop) : Prop :=
  (∀ x, D x → A x) ∧ ∀ x y, D y → A x → R x y → D x

theorem initial_restrict_domain (A D : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hd : DownClosed A R D) (hf : InitialEmbedding F A R B S) :
    InitialEmbedding (fun x y => D x ∧ F x y) D (RestrictOrder R D) B S := by
  refine ⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x y h; exact ⟨h.1,(hf.1.1.1.1 x y h.2).2⟩
  · intro x hx; obtain ⟨y,hy,hxy⟩ := hf.1.1.1.2.1 x (hd.1 x hx)
    exact ⟨y,hy,hx,hxy⟩
  · intro x y z hy hz; exact hf.1.1.1.2.2 x y z hy.2 hz.2
  · intro x z y hx hz; exact hf.1.1.2 x z y hx.2 hz.2
  · intro x y u v hx hy hxy; exact hf.1.2 x y u v hx.2 hy.2 hxy.2.2
  · intro x y z hxy hz hzy
    obtain ⟨w,hwx,hwz⟩ := hf.2 x y z hxy.2 hz hzy
    have hwd := hd.2 w x hxy.1 (hf.1.1.1.1 w z hwz).1 hwx
    exact ⟨w,⟨hwd,hxy.1,hwx⟩,hwd,hwz⟩

theorem partial_initial_agree (A D E : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F G : σ → τ → Prop)
    (hw : WellOrderOn A R) (hs : StrictOrderOn B S)
    (hd : DownClosed A R D) (he : DownClosed A R E)
    (hf : InitialEmbedding F D (RestrictOrder R D) B S)
    (hg : InitialEmbedding G E (RestrictOrder R E) B S)
    (x : σ) (hxD : D x) (hxE : E x) (u v : τ) (hxu : F x u) (hxv : G x v) : u = v := by
  let I : σ → Prop := fun x => D x ∧ E x
  have hif : InitialEmbedding (fun x y => I x ∧ F x y) I (RestrictOrder R I) B S := by
    refine ⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
    · intro x y h; exact ⟨h.1,(hf.1.1.1.1 x y h.2).2⟩
    · intro x hx; obtain ⟨y,hy,hxy⟩ := hf.1.1.1.2.1 x hx.1; exact ⟨y,hy,hx,hxy⟩
    · intro x y z hy hz; exact hf.1.1.1.2.2 x y z hy.2 hz.2
    · intro x z y hx hz; exact hf.1.1.2 x z y hx.2 hz.2
    · intro x y u v hx hy hxy; exact hf.1.2 x y u v hx.2 hy.2 ⟨hx.1.1,hy.1.1,hxy.2.2⟩
    · intro x y z hxy hz hzy
      obtain ⟨w,hwx,hwz⟩ := hf.2 x y z hxy.2 hz hzy
      have hwi : I w := ⟨hwx.1,he.2 w x hxy.1.2 (hd.1 w hwx.1) hwx.2.2⟩
      exact ⟨w,⟨hwi,hxy.1,hwx.2.2⟩,hwi,hwz⟩
  have hig : InitialEmbedding (fun x y => I x ∧ G x y) I (RestrictOrder R I) B S := by
    refine ⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
    · intro x y h; exact ⟨h.1,(hg.1.1.1.1 x y h.2).2⟩
    · intro x hx; obtain ⟨y,hy,hxy⟩ := hg.1.1.1.2.1 x hx.2; exact ⟨y,hy,hx,hxy⟩
    · intro x y z hy hz; exact hg.1.1.1.2.2 x y z hy.2 hz.2
    · intro x z y hx hz; exact hg.1.1.2 x z y hx.2 hz.2
    · intro x y u v hx hy hxy; exact hg.1.2 x y u v hx.2 hy.2 ⟨hx.1.2,hy.1.2,hxy.2.2⟩
    · intro x y z hxy hz hzy
      obtain ⟨w,hwx,hwz⟩ := hg.2 x y z hxy.2 hz hzy
      have hwi : I w := ⟨hd.2 w x hxy.1.1 (he.1 w hwx.1) hwx.2.2,hwx.1⟩
      exact ⟨w,⟨hwi,hxy.1,hwx.2.2⟩,hwi,hwz⟩
  exact initial_embeddings_agree I B (RestrictOrder R I) S _ _
    (wellOrder_restrict A I R hw (fun x hx => hd.1 x hx.1)) hs hif hig x ⟨hxD,hxE⟩ u v ⟨⟨hxD,hxE⟩,hxu⟩ ⟨⟨hxD,hxE⟩,hxv⟩

def ComparisonMap (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop) : σ → τ → Prop :=
  fun x y => ∃ D F, DownClosed A R D ∧ InitialEmbedding F D (RestrictOrder R D) B S ∧ F x y
def ComparisonDomain (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop) : σ → Prop :=
  fun x => ∃ y, ComparisonMap A R B S x y

theorem comparison_bounds (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop)
    (x : σ) (y : τ) (h : ComparisonMap A R B S x y) : A x ∧ B y := by
  obtain ⟨D,F,hd,hf,hxy⟩ := h
  exact ⟨hd.1 x (hf.1.1.1.1 x y hxy).1,(hf.1.1.1.1 x y hxy).2⟩
theorem comparison_functional (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop)
    (hw : WellOrderOn A R) (hs : StrictOrderOn B S) :
    ∀ x u v, ComparisonMap A R B S x u → ComparisonMap A R B S x v → u = v := by
  intro x u v hu hv
  obtain ⟨D,F,hd,hf,hxu⟩ := hu
  obtain ⟨E,G,he,hg,hxv⟩ := hv
  exact partial_initial_agree A D E R B S F G hw hs hd he hf hg x
    (hf.1.1.1.1 x u hxu).1 (hg.1.1.1.1 x v hxv).1 u v hxu hxv

theorem comparison_downclosed (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop) :
    DownClosed A R (ComparisonDomain A R B S) := by
  refine ⟨fun x hx => hx.elim fun y hy => (comparison_bounds A R B S x y hy).1,?_⟩
  intro x y hy hx hxy
  obtain ⟨v,D,F,hd,hf,hyv⟩ := hy
  have hxd := hd.2 x y (hf.1.1.1.1 y v hyv).1 hx hxy
  obtain ⟨u,hu,hxu⟩ := hf.1.1.1.2.1 x hxd
  exact ⟨u,D,F,hd,hf,hxu⟩

theorem comparison_increasing (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop)
    (hw : WellOrderOn A R) (hs : StrictOrderOn B S) :
    ∀ x y u v, ComparisonMap A R B S x u → ComparisonMap A R B S y v → R x y → S u v := by
  intro x y u v hx hy hxy
  obtain ⟨D,F,hd,hf,hyv⟩ := hy
  have hxd := hd.2 x y (hf.1.1.1.1 y v hyv).1 (comparison_bounds A R B S x u hx).1 hxy
  obtain ⟨z,hz,hxz⟩ := hf.1.1.1.2.1 x hxd
  have he := comparison_functional A R B S hw hs x u z hx ⟨D,F,hd,hf,hxz⟩
  exact he.symm ▸ hf.1.2 x y z v hxz hyv ⟨hxd,(hf.1.1.1.1 y v hyv).1,hxy⟩

theorem comparison_initial (A : σ → Prop) (R : σ → σ → Prop) (B : τ → Prop) (S : τ → τ → Prop)
    (hw : WellOrderOn A R) (hs : StrictOrderOn B S) :
    InitialEmbedding (ComparisonMap A R B S) (ComparisonDomain A R B S)
      (RestrictOrder R (ComparisonDomain A R B S)) B S := by
  refine ⟨⟨⟨⟨?_,?_,comparison_functional A R B S hw hs⟩,?_⟩,?_⟩,?_⟩
  · intro x y h; exact ⟨⟨y,h⟩,(comparison_bounds A R B S x y h).2⟩
  · intro x hx; obtain ⟨y,hy⟩ := hx; exact ⟨y,(comparison_bounds A R B S x y hy).2,hy⟩
  · intro x z y hx hz
    obtain he | hxz | hzx := hw.1.2.2.2 x z (comparison_bounds A R B S x y hx).1 (comparison_bounds A R B S z y hz).1
    · exact he
    · exact (hs.2.1 y (comparison_bounds A R B S x y hx).2 (comparison_increasing A R B S hw hs x z y y hx hz hxz)).elim
    · exact (hs.2.1 y (comparison_bounds A R B S x y hx).2 (comparison_increasing A R B S hw hs z x y y hz hx hzx)).elim
  · intro x y u v hx hy hxy; exact comparison_increasing A R B S hw hs x y u v hx hy hxy.2.2
  · intro x y z hxy hz hzy
    obtain ⟨D,F,hd,hf,hxy⟩ := hxy
    obtain ⟨w,hwx,hwz⟩ := hf.2 x y z hxy hz hzy
    exact ⟨w,⟨⟨z,D,F,hd,hf,hwz⟩,⟨y,D,F,hd,hf,hxy⟩,hwx.2.2⟩,D,F,hd,hf,hwz⟩
#classicism_check initial_restrict_domain partial_initial_agree comparison_bounds comparison_functional comparison_downclosed comparison_increasing comparison_initial
#classicism_types initial_restrict_domain partial_initial_agree comparison_bounds comparison_functional comparison_downclosed comparison_increasing comparison_initial
end Classicism.MathematicalContingency
