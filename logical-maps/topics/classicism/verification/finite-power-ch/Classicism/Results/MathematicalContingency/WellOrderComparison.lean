import Classicism.Results.MathematicalContingency.ComparisonConstruction
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
theorem downclosed_cut (A D : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) (hd : DownClosed A R D) (hne : ∃ x, A x ∧ ¬ D x) :
    ∃ a, A a ∧ ¬ D a ∧ ∀ x, A x → (R x a ↔ D x) := by
  obtain ⟨a,ha,hm⟩ := hw.2 (fun x => A x ∧ ¬ D x) (fun _ h => h.1) hne
  refine ⟨a,ha.1,ha.2,?_⟩
  intro x hx
  constructor
  · intro hxa
    exact (em (D x)).elim (fun h => h) (fun h => (hm x ⟨hx,h⟩ hxa).elim)
  · intro hdx
    obtain he | hxa | hax := hw.1.2.2.2 x a hx ha.1
    · exact (ha.2 (he ▸ hdx)).elim
    · exact hxa
    · exact (ha.2 (hd.2 a x hdx ha.1 hax)).elim

theorem initial_extend_cut (A D : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hw : WellOrderOn A R) (hs : WellOrderOn B S)
    (hd : DownClosed A R D) (hf : InitialEmbedding F D (RestrictOrder R D) B S)
    (a : σ) (b : τ) (ha : A a) (hb : B b) (hna : ¬ D a) (hnb : ¬ ∃ x, F x b)
    (ca : ∀ x, A x → (R x a ↔ D x)) (cb : ∀ y, B y → (S y b ↔ ∃ x, F x y)) :
    DownClosed A R (fun x => D x ∨ x = a) ∧
    InitialEmbedding (fun x y => F x y ∨ (x = a ∧ y = b)) (fun x => D x ∨ x = a)
      (RestrictOrder R (fun x => D x ∨ x = a)) B S := by
  let P : σ → Prop := fun x => D x ∨ x = a
  have hpd : DownClosed A R P := by
    refine ⟨fun x hx => hx.elim (hd.1 x) (fun he => he.symm ▸ ha),?_⟩
    intro x y hy hx hxy
    exact hy.elim (fun hy => Or.inl (hd.2 x y hy hx hxy))
      (fun he => Or.inl ((ca x hx).mp (he ▸ hxy)))
  refine ⟨hpd,⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩⟩
  · intro x y h
    exact h.elim (fun h => ⟨Or.inl (hf.1.1.1.1 x y h).1,(hf.1.1.1.1 x y h).2⟩)
      (fun h => ⟨Or.inr h.1,h.2.symm ▸ hb⟩)
  · intro x hx
    refine hx.elim ?_ ?_
    · intro hx; obtain ⟨y,hy,hxy⟩ := hf.1.1.1.2.1 x hx
      exact ⟨y,hy,Or.inl hxy⟩
    · intro he; exact ⟨b,hb,Or.inr ⟨he,rfl⟩⟩
  · intro x y z hy hz
    exact hy.elim (fun hy => hz.elim (hf.1.1.1.2.2 x y z hy)
      (fun hz => (hna (hz.1 ▸ (hf.1.1.1.1 x y hy).1)).elim))
      (fun hy => hz.elim (fun hz => (hna (hy.1 ▸ (hf.1.1.1.1 x z hz).1)).elim)
        (fun hz => hy.2.trans hz.2.symm))
  · intro x z y hx hz
    exact hx.elim (fun hx => hz.elim (hf.1.1.2 x z y hx)
      (fun hz => (hnb ⟨x,hz.2 ▸ hx⟩).elim))
      (fun hx => hz.elim (fun hz => (hnb ⟨z,hx.2 ▸ hz⟩).elim)
        (fun hz => hx.1.trans hz.1.symm))
  · intro x y u v hx hy hxy
    obtain hx | ⟨hxa,hub⟩ := hx
    · obtain hy | ⟨hya,hvb⟩ := hy
      · exact hf.1.2 x y u v hx hy ⟨(hf.1.1.1.1 x u hx).1,(hf.1.1.1.1 y v hy).1,hxy.2.2⟩
      · exact hvb.symm ▸ (cb u (hf.1.1.1.1 x u hx).2).mpr ⟨x,hx⟩
    · obtain hy | ⟨hya,hvb⟩ := hy
      · have hyD := (hf.1.1.1.1 y v hy).1
        have hay : R a y := hxa ▸ hxy.2.2
        have hya := (ca y (hd.1 y hyD)).mpr hyD
        exact (hw.1.2.1 a ha (hw.1.2.2.1 a y a ha (hd.1 y hyD) ha hay hya)).elim
      · have hay : R a y := hxa ▸ hxy.2.2
        exact (hw.1.2.1 a ha (hya ▸ hay)).elim
  · intro x y z hxy hz hzy
    obtain hxy | ⟨hxa,hyb⟩ := hxy
    · obtain ⟨w,hwx,hwz⟩ := hf.2 x y z hxy hz hzy
      exact ⟨w,⟨Or.inl hwx.1,Or.inl hwx.2.1,hwx.2.2⟩,Or.inl hwz⟩
    · obtain ⟨w,hwz⟩ := (cb z hz).mp (hyb ▸ hzy)
      have hwD := (hf.1.1.1.1 w z hwz).1
      have hwa := (ca w (hd.1 w hwD)).mpr hwD
      exact ⟨w,⟨Or.inl hwD,Or.inr hxa,hxa.symm ▸ hwa⟩,Or.inl hwz⟩

theorem initial_full_domain (A D : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hd : DownClosed A R D) (hf : InitialEmbedding F D (RestrictOrder R D) B S)
    (hfull : ∀ x, A x → D x) : InitialEmbedding F A R B S := by
  refine ⟨⟨⟨⟨?_,?_,hf.1.1.1.2.2⟩,hf.1.1.2⟩,?_⟩,?_⟩
  · intro x y h; exact ⟨hd.1 x (hf.1.1.1.1 x y h).1,(hf.1.1.1.1 x y h).2⟩
  · intro x hx; exact hf.1.1.1.2.1 x (hfull x hx)
  · intro x y u v hx hy hxy
    exact hf.1.2 x y u v hx hy ⟨(hf.1.1.1.1 x u hx).1,(hf.1.1.1.1 y v hy).1,hxy⟩
  · intro x y z hxy hz hzy
    obtain ⟨w,hwx,hwz⟩ := hf.2 x y z hxy hz hzy
    exact ⟨w,hwx.2.2,hwz⟩

theorem initial_full_range (A D : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hd : DownClosed A R D) (hf : InitialEmbedding F D (RestrictOrder R D) B S)
    (hfull : ∀ y, B y → ∃ x, F x y) : InitialEmbedding (fun y x => F x y) B S A R := by
  refine ⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro y x h; exact ⟨(hf.1.1.1.1 x y h).2,hd.1 x (hf.1.1.1.1 x y h).1⟩
  · intro y hy; obtain ⟨x,hxy⟩ := hfull y hy
    exact ⟨x,hd.1 x (hf.1.1.1.1 x y hxy).1,hxy⟩
  · intro y x z hx hz; exact hf.1.1.2 x z y hx hz
  · intro y z x hy hz; exact hf.1.1.1.2.2 x y z hy hz
  · intro u v x y hxu hyv huv
    obtain ⟨w,hwx,hwv⟩ := hf.2 y v u hyv (hf.1.1.1.1 x u hxu).2 huv
    have heq := hf.1.1.2 w x u hwv hxu
    exact heq ▸ hwx.2.2
  · intro y x z hxy hz hzx
    have hzD := hd.2 z x (hf.1.1.1.1 x y hxy).1 hz hzx
    obtain ⟨w,hw,hzw⟩ := hf.1.1.1.2.1 z hzD
    exact ⟨w,hf.1.2 z x w y hzw hxy ⟨hzD,(hf.1.1.1.1 x y hxy).1,hzx⟩,hzw⟩

theorem initial_range_downclosed (D : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hf : InitialEmbedding F D R B S) : DownClosed B S (fun y => ∃ x, F x y) := by
  refine ⟨fun y hy => hy.elim fun x hx => (hf.1.1.1.1 x y hx).2,?_⟩
  intro y z hz hy hyz
  obtain ⟨x,hxz⟩ := hz
  obtain ⟨w,_,hwy⟩ := hf.2 x z y hxz hy hyz
  exact ⟨w,hwy⟩

theorem comparison_domain_or_range_full (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (hw : WellOrderOn A R) (hs : WellOrderOn B S)
    (hd : DownClosed A R (ComparisonDomain A R B S))
    (hf : InitialEmbedding (ComparisonMap A R B S) (ComparisonDomain A R B S)
      (RestrictOrder R (ComparisonDomain A R B S)) B S) :
    (∀ x, A x → ComparisonDomain A R B S x) ∨
    (∀ y, B y → ∃ x, ComparisonMap A R B S x y) := by
  let F := ComparisonMap A R B S
  let D := ComparisonDomain A R B S
  let E : τ → Prop := fun y => ∃ x, F x y
  have he : DownClosed B S E := initial_range_downclosed D (RestrictOrder R D) B S F hf
  refine (em (∀ x, A x → D x)).elim Or.inl ?_
  intro hnot
  have hex : ∃ x, A x ∧ ¬ D x := (em (∃ x, A x ∧ ¬ D x)).elim (fun h => h)
    (fun h => (hnot (fun x hx => (em (D x)).elim (fun h => h) (fun hn => (h ⟨x,hx,hn⟩).elim))).elim)
  obtain ⟨a,ha,hna,ca⟩ := downclosed_cut A D R hw hd hex
  apply Or.inr
  intro y hy
  refine (em (E y)).elim (fun h => h) ?_
  intro hn
  obtain ⟨b,hb,hnb,cb⟩ := downclosed_cut B E S hs he ⟨y,hy,hn⟩
  have ext := initial_extend_cut A D R B S F hw hs hd hf a b ha hb hna hnb ca cb
  have hab : F a b := ⟨(fun x => D x ∨ x = a),(fun x y => F x y ∨ (x = a ∧ y = b)),
    ext.1,ext.2,Or.inr ⟨rfl,rfl⟩⟩
  exact (hna ⟨b,hab⟩).elim

theorem wellOrder_comparison (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (hw : WellOrderOn A R) (hs : WellOrderOn B S) :
    (∃ F, InitialEmbedding F A R B S) ∨ (∃ G, InitialEmbedding G B S A R) := by
  obtain hfull | hfull := comparison_domain_or_range_full A R B S hw hs
    (comparison_downclosed A R B S) (comparison_initial A R B S hw hs.1)
  · exact Or.inl ⟨ComparisonMap A R B S,initial_full_domain A (ComparisonDomain A R B S) R B S
      (ComparisonMap A R B S) (comparison_downclosed A R B S) (comparison_initial A R B S hw hs.1) hfull⟩
  · exact Or.inr ⟨fun y x => ComparisonMap A R B S x y,initial_full_range A (ComparisonDomain A R B S) R B S
      (ComparisonMap A R B S) (comparison_downclosed A R B S) (comparison_initial A R B S hw hs.1) hfull⟩
#classicism_check downclosed_cut initial_extend_cut initial_full_domain initial_full_range initial_range_downclosed comparison_domain_or_range_full wellOrder_comparison
#classicism_types downclosed_cut initial_extend_cut initial_full_domain initial_full_range initial_range_downclosed comparison_domain_or_range_full wellOrder_comparison
end Classicism.MathematicalContingency
