import Classicism.Results.MathematicalContingency.StableTransport

/-! Maps and injections transported over rigid ND domains.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem rigid_map_domain (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (ha : Rigid A) (hb : Rigid B) (hf : Rigid F) (hm : Maps F A B) :
    □ (∀ x y, F x y → A x ∧ B y) :=
  restricted_barcan F (fun x y => A x ∧ B y) hf.2 (fun x y h =>
    modal_K _ _ (modal_K _ _ (nec% (fun (hx : A x) (hy : B y) => And.intro hx hy))
      (box_elim ha.1 x (hm.1 x y h).1)) (box_elim hb.1 y (hm.1 x y h).2))

theorem rigid_map_total (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (ha : Rigid A) (hb : Rigid B) (hf : Rigid F) (hm : Maps F A B) :
    □ (∀ x, A x → ∃ y, B y ∧ F x y) :=
  restricted_barcan_unary A (fun x => ∃ y, B y ∧ F x y) ha (by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hm.2.1 x hx
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hy : B y) (hxy : F x y) => (show ∃ y, B y ∧ F x y from ⟨y,hy,hxy⟩)))
      (box_elim hb.1 y hy)) (box_elim hf.1 x y hxy))

theorem rigid_map_functional (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (hf : Rigid F) (nd : DomainND A) (hm : Maps F A B) :
    □ (∀ x y z, F x y → F x z → y = z) := by
  have h : □ (∀ x y, F x y → ∀ u v, F u v → x = u → y = v) :=
    restricted_barcan F (fun x y => ∀ u v, F u v → x = u → y = v) hf.2 (by
      intro x y hxy
      exact restricted_barcan F (fun u v => x = u → y = v) hf.2 (by
        intro u v huv
        obtain e | e := em (x = u)
        · subst u
          exact box_imp_of_box _ _ (necessity_of_identity y v (hm.2.2 x y v hxy huv))
        · exact box_imp_of_box_not _ _ (nd x u (hm.1 x y hxy).1 (hm.1 u v huv).1 e)))
  exact modal_K _ _ (nec% (fun (h : ∀ x y, F x y → ∀ u v, F u v → x = u → y = v)
    x y z hxy hxz => h x y hxy x z hxz rfl)) h

theorem rigid_maps_necessary (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (ha : Rigid A) (hb : Rigid B) (hf : Rigid F) (nd : DomainND A) (hm : Maps F A B) :
    □ (Maps F A B) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hd : ∀ x y, F x y → A x ∧ B y) (ht : ∀ x, A x → ∃ y, B y ∧ F x y)
      (hu : ∀ x y z, F x y → F x z → y = z) => (show Maps F A B from ⟨hd,ht,hu⟩)))
      (rigid_map_domain A B F ha hb hf hm)) (rigid_map_total A B F ha hb hf hm))
      (rigid_map_functional A B F hf nd hm)

theorem rigid_injection_injective (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (hf : Rigid F) (nd : DomainND B) (hi : Injects F A B) :
    □ (∀ x u y, F x y → F u y → x = u) := by
  have h : □ (∀ x y, F x y → ∀ u v, F u v → y = v → x = u) :=
    restricted_barcan F (fun x y => ∀ u v, F u v → y = v → x = u) hf.2 (by
      intro x y hxy
      exact restricted_barcan F (fun u v => y = v → x = u) hf.2 (by
        intro u v huv
        obtain e | e := em (y = v)
        · subst v
          exact box_imp_of_box _ _ (necessity_of_identity x u (hi.2 x u y hxy huv))
        · exact box_imp_of_box_not _ _ (nd y v (hi.1.1 x y hxy).2 (hi.1.1 u v huv).2 e)))
  exact modal_K _ _ (nec% (fun (h : ∀ x y, F x y → ∀ u v, F u v → y = v → x = u)
    x u y hxy huy => h x y hxy u y huy rfl)) h

theorem rigid_injects_necessary (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (ha : Rigid A) (hb : Rigid B) (hf : Rigid F) (ndA : DomainND A) (ndB : DomainND B)
    (hi : Injects F A B) : □ (Injects F A B) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (hm : Maps F A B) (hi : ∀ x u y, F x y → F u y → x = u) =>
      (show Injects F A B from ⟨hm,hi⟩))) (rigid_maps_necessary A B F ha hb hf ndA hi.1))
      (rigid_injection_injective A B F hf ndB hi)

theorem embedding_has_necessary_rigid_witness (A : α → Prop) (B : β → Prop)
    (ha : Rigid A) (hb : Rigid B) (ndA : DomainND A) (ndB : DomainND B)
    (rc : P.RigidComprehension (α → β → Prop)) (he : Embeds A B) :
    ∃ F, Rigid F ∧ □ (Injects F A B) := by
  obtain ⟨F,hF⟩ := he
  obtain ⟨G,hG,e⟩ := rc F
  have hm : Maps G A B := ⟨fun x y h => hF.1.1 x y ((e x y).mpr h),
    fun x hx => (hF.1.2.1 x hx).elim fun y hy => ⟨y,hy.1,(e x y).mp hy.2⟩,
    fun x y z hy hz => hF.1.2.2 x y z ((e x y).mpr hy) ((e x z).mpr hz)⟩
  have hi : Injects G A B := ⟨hm,fun x u y hx hu => hF.2 x u y ((e x y).mpr hx) ((e u y).mpr hu)⟩
  exact ⟨G,hG,rigid_injects_necessary A B G ha hb hG ndA ndB hi⟩

#classicism_check rigid_map_domain rigid_map_total rigid_map_functional rigid_maps_necessary rigid_injection_injective rigid_injects_necessary embedding_has_necessary_rigid_witness
#classicism_types rigid_map_domain rigid_map_total rigid_map_functional rigid_maps_necessary rigid_injection_injective rigid_injects_necessary embedding_has_necessary_rigid_witness
end Classicism.MathematicalContingency
