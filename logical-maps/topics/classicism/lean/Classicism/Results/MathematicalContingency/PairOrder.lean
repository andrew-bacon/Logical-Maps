import Classicism.Results.MathematicalContingency.RigidPairs

/-! Maximum-first lexicographic order on rigid pair objects.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

def OrderLe (L : α → α → Prop) (x y : α) : Prop := x = y ∨ L x y

theorem orderLe_trans (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (x y z : α) (hx : A x) (hy : A y) (hz : A z)
    (h : OrderLe L x y) (k : OrderLe L y z) : OrderLe L x z := by
  obtain e | h := h
  · subst y; exact k
  · obtain e | k := k
    · subst z; exact Or.inr h
    · exact Or.inr (hs.2.2.1 x y z hx hy hz h k)

theorem orderLe_antisymm (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (x y : α) (hx : A x) (hy : A y) (h : OrderLe L x y) (k : OrderLe L y x) : x = y := by
  obtain e | h := h
  · exact e
  · obtain e | k := k
    · exact e.symm
    · exact (hs.2.1 x hx (hs.2.2.1 x y x hx hy hx h k)).elim

def LexTriple (L : α → α → Prop) (m x y n u v : α) : Prop :=
  L m n ∨ m = n ∧ (L x u ∨ x = u ∧ L y v)

theorem lexTriple_irrefl (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (m x y : α) (hm : A m) (hx : A x) (hy : A y) : ¬ LexTriple L m x y m x y :=
  fun h => h.elim (hs.2.1 m hm) (fun h => h.2.elim (hs.2.1 x hx) (fun h => hs.2.1 y hy h.2))

theorem lexTriple_trans (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (m x y n u v p a b : α) (hm : A m) (hx : A x) (hy : A y)
    (hn : A n) (hu : A u) (hv : A v) (hp : A p) (ha : A a) (hb : A b)
    (h : LexTriple L m x y n u v) (k : LexTriple L n u v p a b) : LexTriple L m x y p a b := by
  obtain h | ⟨e,h⟩ := h
  · obtain k | ⟨e,_⟩ := k
    · exact Or.inl (hs.2.2.1 m n p hm hn hp h k)
    · subst p; exact Or.inl h
  · subst n
    obtain k | ⟨e,k⟩ := k
    · exact Or.inl k
    · subst p
      refine Or.inr ⟨rfl,?_⟩
      obtain h | ⟨e,h⟩ := h
      · obtain k | ⟨e,_⟩ := k
        · exact Or.inl (hs.2.2.1 x u a hx hu ha h k)
        · subst a; exact Or.inl h
      · subst u
        obtain k | ⟨e,k⟩ := k
        · exact Or.inl k
        · subst a
          exact Or.inr ⟨rfl,hs.2.2.1 y v b hy hv hb h k⟩

theorem lexTriple_total (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (m x y n u v : α) (hm : A m) (hx : A x) (hy : A y) (hn : A n) (hu : A u) (hv : A v) :
    (m = n ∧ x = u ∧ y = v) ∨ LexTriple L m x y n u v ∨ LexTriple L n u v m x y := by
  obtain e | h | h := hs.2.2.2 m n hm hn
  · subst n
    obtain e | h | h := hs.2.2.2 x u hx hu
    · subst u
      obtain e | h | h := hs.2.2.2 y v hy hv
      · exact Or.inl ⟨rfl,rfl,e⟩
      · exact Or.inr (Or.inl (Or.inr ⟨rfl,Or.inr ⟨rfl,h⟩⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,Or.inr ⟨rfl,h⟩⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨rfl,Or.inl h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,Or.inl h⟩))
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl h))

def PairMaxAt (A : α → Prop) (L : α → α → Prop) (P : α → α → Prop) (m x y : α) : Prop :=
  PairAt A P x y ∧ (m = x ∨ m = y) ∧ OrderLe L x m ∧ OrderLe L y m

def MaxPairOrder (A : α → Prop) (L : α → α → Prop) (P Q : α → α → Prop) : Prop :=
  ∃ m x y n u v, PairMaxAt A L P m x y ∧ PairMaxAt A L Q n u v ∧ LexTriple L m x y n u v

theorem pairMaxAt_member (A : α → Prop) (L : α → α → Prop) (P : α → α → Prop) (m x y : α)
    (h : PairMaxAt A L P m x y) : A m := h.2.1.elim (fun e => e ▸ h.1.1) (fun e => e ▸ h.1.2.1)

theorem pairMaxAt_exists (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (P : α → α → Prop) (h : PairCarrier A P) : ∃ m x y, PairMaxAt A L P m x y := by
  obtain ⟨x,y,hP⟩ := h
  obtain e | h | h := hs.2.2.2 x y hP.1 hP.2.1
  · subst y
    exact ⟨x,x,x,hP,Or.inl rfl,Or.inl rfl,Or.inl rfl⟩
  · exact ⟨y,x,y,hP,Or.inr rfl,Or.inr h,Or.inl rfl⟩
  · exact ⟨x,x,y,hP,Or.inl rfl,Or.inl rfl,Or.inr h⟩

theorem pairMaxAt_unique (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (P : α → α → Prop) (m x y n u v : α)
    (h : PairMaxAt A L P m x y) (k : PairMaxAt A L P n u v) : m = n ∧ x = u ∧ y = v := by
  obtain ⟨ex,ey⟩ := pairAt_coordinates A P x y u v h.1 k.1
  subst u; subst v
  have hmn : OrderLe L m n := h.2.1.elim (fun e => e ▸ k.2.2.1) (fun e => e ▸ k.2.2.2)
  have hnm : OrderLe L n m := k.2.1.elim (fun e => e ▸ h.2.2.1) (fun e => e ▸ h.2.2.2)
  exact ⟨orderLe_antisymm A L hs m n (pairMaxAt_member A L P m x y h)
    (pairMaxAt_member A L P n x y k) hmn hnm,rfl,rfl⟩

theorem maxPairOrder_at (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L)
    (P Q : α → α → Prop) (m x y n u v : α)
    (h : PairMaxAt A L P m x y) (k : PairMaxAt A L Q n u v) :
    MaxPairOrder A L P Q ↔ LexTriple L m x y n u v := by
  constructor
  · intro ⟨m',x',y',n',u',v',h',k',hlt⟩
    obtain ⟨em,ex,ey⟩ := pairMaxAt_unique A L hs P m x y m' x' y' h h'
    obtain ⟨en,eu,ev⟩ := pairMaxAt_unique A L hs Q n u v n' u' v' k k'
    subst m'; subst x'; subst y'; subst n'; subst u'; subst v'
    exact hlt
  · intro hlt; exact ⟨m,x,y,n,u,v,h,k,hlt⟩

theorem maxPairOrder_strict (A : α → Prop) (L : α → α → Prop) (hs : StrictOrderOn A L) :
    StrictOrderOn (PairCarrier A) (MaxPairOrder A L) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro P Q ⟨m,x,y,n,u,v,h,k,_⟩; exact ⟨⟨x,y,h.1⟩,⟨u,v,k.1⟩⟩
  · intro P hp hh
    obtain ⟨m,x,y,h⟩ := pairMaxAt_exists A L hs P hp
    exact lexTriple_irrefl A L hs m x y (pairMaxAt_member A L P m x y h) h.1.1 h.1.2.1
      ((maxPairOrder_at A L hs P P m x y m x y h h).mp hh)
  · intro P Q R hp hq hr hpq hqr
    obtain ⟨m,x,y,h⟩ := pairMaxAt_exists A L hs P hp
    obtain ⟨n,u,v,k⟩ := pairMaxAt_exists A L hs Q hq
    obtain ⟨p,a,b,j⟩ := pairMaxAt_exists A L hs R hr
    exact (maxPairOrder_at A L hs P R m x y p a b h j).mpr
      (lexTriple_trans A L hs m x y n u v p a b
        (pairMaxAt_member A L P m x y h) h.1.1 h.1.2.1
        (pairMaxAt_member A L Q n u v k) k.1.1 k.1.2.1
        (pairMaxAt_member A L R p a b j) j.1.1 j.1.2.1
        ((maxPairOrder_at A L hs P Q m x y n u v h k).mp hpq)
        ((maxPairOrder_at A L hs Q R n u v p a b k j).mp hqr))
  · intro P Q hp hq
    obtain ⟨m,x,y,h⟩ := pairMaxAt_exists A L hs P hp
    obtain ⟨n,u,v,k⟩ := pairMaxAt_exists A L hs Q hq
    obtain ⟨_,ex,ey⟩ | hlt | hlt := lexTriple_total A L hs m x y n u v
      (pairMaxAt_member A L P m x y h) h.1.1 h.1.2.1
      (pairMaxAt_member A L Q n u v k) k.1.1 k.1.2.1
    · subst u; subst v; exact Or.inl (pairAt_unique A P Q x y h.1 k.1)
    · exact Or.inr (Or.inl ((maxPairOrder_at A L hs P Q m x y n u v h k).mpr hlt))
    · exact Or.inr (Or.inr ((maxPairOrder_at A L hs Q P n u v m x y k h).mpr hlt))

#classicism_check orderLe_trans orderLe_antisymm lexTriple_irrefl lexTriple_trans lexTriple_total pairMaxAt_member pairMaxAt_exists pairMaxAt_unique maxPairOrder_at maxPairOrder_strict
#classicism_types orderLe_trans orderLe_antisymm lexTriple_irrefl lexTriple_trans lexTriple_total pairMaxAt_member pairMaxAt_exists pairMaxAt_unique maxPairOrder_at maxPairOrder_strict
end Classicism.MathematicalContingency
