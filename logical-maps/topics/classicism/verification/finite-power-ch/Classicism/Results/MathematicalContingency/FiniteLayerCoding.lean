import Classicism.Results.MathematicalContingency.FiniteRanks
namespace Classicism.MathematicalContingency
variable {σ α : Type} [Ty σ] [Ty α]

def LeastLayer (X : α → Prop) (D : ((σ → Prop) → Prop) → α → Prop)
    (x : α) (n : (σ → Prop) → Prop) : Prop :=
  LeastRelated X LowerNat LowerLT (fun x n => D n x) x n

def LayerCode (X : α → Prop) (L : α → α → Prop) (D : ((σ → Prop) → Prop) → α → Prop)
    (x : α) (k : (σ → Prop) → Prop) : Prop :=
  ∃ n r, LeastLayer X D x n ∧ FiniteRank (D n) L x r ∧ LowerPair n r k

theorem leastLayer_total (hp : LowerPeano σ) (X : α → Prop) (D : ((σ → Prop) → Prop) → α → Prop)
    (cover : ∀ x, X x → ∃ n, LowerNat n ∧ D n x) (x : α) (hx : X x) :
    ∃ n, LeastLayer X D x n :=
  leastRelated_exists X LowerNat LowerLT (fun x n => D n x) (lowerNat_wellOrder hp) cover x hx

theorem leastLayer_unique (hp : LowerPeano σ) (X : α → Prop) (D : ((σ → Prop) → Prop) → α → Prop)
    (x : α) (n m : (σ → Prop) → Prop) (hn : LeastLayer X D x n) (hm : LeastLayer X D x m) : n = m :=
  leastRelated_unique X LowerNat LowerLT (fun x n => D n x) (lowerNat_wellOrder hp) x n m hn hm

theorem layerCode_data (X : α → Prop) (L : α → α → Prop) (D : ((σ → Prop) → Prop) → α → Prop)
    (x : α) (k : (σ → Prop) → Prop) (h : LayerCode X L D x k) : X x ∧ LowerNat k := by
  obtain ⟨n,r,hn,_,hk⟩ := h
  exact ⟨hn.1,(lowerPair_numbers n r k hk).2.2⟩

theorem layerCode_total (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (D : ((σ → Prop) → Prop) → α → Prop) (hw : WellOrderOn A L)
    (finite : ∀ n, LowerNat n → FiniteSubset A (D n))
    (cover : ∀ x, X x → ∃ n, LowerNat n ∧ D n x) (x : α) (hx : X x) :
    ∃ k, LowerNat k ∧ LayerCode X L D x k := by
  obtain ⟨n,hn⟩ := leastLayer_total hp X D cover x hx
  obtain ⟨r,hr⟩ := finiteRank_total hp A (D n) L hw (finite n hn.2.1) x hn.2.2.1
  obtain ⟨k,hk,hpair⟩ := lowerPair_total n r hn.2.1 hr.2.1
  exact ⟨k,hk,n,r,hn,hr,hpair⟩

theorem layerCode_functional (hp : LowerPeano σ) (X : α → Prop) (L : α → α → Prop)
    (D : ((σ → Prop) → Prop) → α → Prop) (x : α) (k l : (σ → Prop) → Prop)
    (hk : LayerCode X L D x k) (hl : LayerCode X L D x l) : k = l := by
  obtain ⟨n,r,hn,hr,hk⟩ := hk
  obtain ⟨m,s,hm,hs,hl⟩ := hl
  have e := leastLayer_unique hp X D x n m hn hm
  have hs' : FiniteRank (D n) L x s := e.symm ▸ hs
  have er := finiteRank_functional hp (D n) L x r s hr hs'
  have hl' : LowerPair n r l := e.symm ▸ er.symm ▸ hl
  exact lowerPair_functional hp n r k l hk hl'

theorem layerCode_injective (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (D : ((σ → Prop) → Prop) → α → Prop) (hl : StrictOrderOn A L)
    (sub : ∀ n x, LowerNat n → D n x → A x) (x y : α) (k : (σ → Prop) → Prop)
    (hx : LayerCode X L D x k) (hy : LayerCode X L D y k) : x = y := by
  obtain ⟨n,r,hn,hr,hk⟩ := hx
  obtain ⟨m,s,hm,hs,hk'⟩ := hy
  have e := lowerPair_injective hp n r m s k hk hk'
  have hs' : FiniteRank (D n) L y r := e.1.symm ▸ e.2.symm ▸ hs
  exact finiteRank_injective hp A (D n) L hl (fun a ha => sub n a hn.2.1 ha) x y r hr hs'

/-- A single formula codes every finite-layer cover in a fixed well-order. -/
theorem finiteLayers_injects (hp : LowerPeano σ) (A X : α → Prop) (L : α → α → Prop)
    (D : ((σ → Prop) → Prop) → α → Prop) (hw : WellOrderOn A L)
    (finite : ∀ n, LowerNat n → FiniteSubset A (D n))
    (cover : ∀ x, X x → ∃ n, LowerNat n ∧ D n x) :
    Injects (LayerCode X L D) X (@LowerNat σ _) :=
  ⟨⟨fun x k h => layerCode_data X L D x k h,
    fun x hx => layerCode_total hp A X L D hw finite cover x hx,
    fun x k l hk hl => layerCode_functional hp X L D x k l hk hl⟩,
    fun x y k hx hy => layerCode_injective hp A X L D hw.1
      (fun n x hn hx => finiteSubset_members A (D n) (finite n hn) x hx) x y k hx hy⟩

#classicism_check leastLayer_total leastLayer_unique layerCode_data layerCode_total layerCode_functional layerCode_injective finiteLayers_injects
#classicism_types leastLayer_total leastLayer_unique layerCode_data layerCode_total layerCode_functional layerCode_injective finiteLayers_injects
end Classicism.MathematicalContingency
