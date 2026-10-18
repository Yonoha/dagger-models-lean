import OriginalProductBeadCompletion

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalProductGadget

noncomputable section

open DaggerChosenRigidificationNecklace

/-- The monotone operator determined by two comparable vertices. -/
def pairOrderHom (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    Fin 2 →o Fin (n + 1) where
  toFun := ![a, b]
  monotone' := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    exact hab

def simplexEdge (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    (Δ[1] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk (pairOrderHom n a b hab))

theorem simplexEdge_first (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    SSet.stdSimplex.obj₀Equiv
      ((simplexEdge n a b hab).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = a := by
  rfl

theorem simplexEdge_last (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    SSet.stdSimplex.obj₀Equiv
      ((simplexEdge n a b hab).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = b := by
  rfl

def beadCoord (m : ℕ) (dim : Fin m → ℕ) (i : Fin m)
    (x : (beadSpace.{u} m dim).obj (op ⦋0⦌)) : Fin (dim i + 1) :=
  vertex m (fun j ↦ NecklaceCode.single (dim j)) i x

theorem singleIso_inv_coord (n : ℕ) (x : (Δ[n] : SSet.{u}).obj (op ⦋0⦌)) :
    ((NecklaceCode.single n).verticesEquiv
      ((NecklaceCode.singleIso n).inv.app _ x)).down =
        SSet.stdSimplex.obj₀Equiv x := by
  have h := congrFun
    (NatTrans.congr_app (NecklaceCode.singleIso n).inv_hom_id (op ⦋0⦌)) x
  have hv := NecklaceCode.singleIso_vertex n
    ((NecklaceCode.singleIso n).inv.app _ x)
  change (NecklaceCode.singleIso n).hom.app _
    ((NecklaceCode.singleIso n).inv.app _ x) = x at h
  rw [h] at hv
  exact hv.symm

def beadEdgeComponent (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (i : Fin m) : (Δ[1] : SSet.{u}) ⟶ (NecklaceCode.single (dim i)).toSSet :=
  simplexEdge (dim i) (beadCoord m dim i a) (beadCoord m dim i b) (hab i) ≫
    (NecklaceCode.singleIso (dim i)).inv

theorem beadEdgeComponent_first (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (i : Fin m) :
    (beadEdgeComponent m dim a b hab i).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _ a := by
  apply (NecklaceCode.single (dim i)).verticesEquiv.injective
  apply ULift.ext
  change ((NecklaceCode.single (dim i)).verticesEquiv
    ((NecklaceCode.singleIso (dim i)).inv.app _
      ((simplexEdge (dim i) (beadCoord m dim i a)
        (beadCoord m dim i b) (hab i)).app _
          (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))))).down = beadCoord m dim i a
  rw [singleIso_inv_coord, simplexEdge_first]

theorem beadEdgeComponent_last (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (i : Fin m) :
    (beadEdgeComponent m dim a b hab i).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _ b := by
  apply (NecklaceCode.single (dim i)).verticesEquiv.injective
  apply ULift.ext
  change ((NecklaceCode.single (dim i)).verticesEquiv
    ((NecklaceCode.singleIso (dim i)).inv.app _
      ((simplexEdge (dim i) (beadCoord m dim i a)
        (beadCoord m dim i b) (hab i)).app _
          (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))))).down = beadCoord m dim i b
  rw [singleIso_inv_coord, simplexEdge_last]

theorem beadVertex_ext (m : ℕ) (dim : Fin m → ℕ)
    (x y : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (h : ∀ i : Fin m,
      (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _ x =
        (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _ y) :
    x = y := by
  apply SSet.yonedaEquiv.symm.injective
  apply Pi.hom_ext
  intro i
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp]
  have hx : SSet.yonedaEquiv (SSet.yonedaEquiv.symm x) = x :=
    SSet.yonedaEquiv.apply_symm_apply x
  have hy : SSet.yonedaEquiv (SSet.yonedaEquiv.symm y) = y :=
    SSet.yonedaEquiv.apply_symm_apply y
  exact (congrArg (fun z ↦
    (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _ z) hx).trans
    ((h i).trans (congrArg (fun z ↦
      (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _ z) hy).symm)

def beadEdgeMap (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    (Δ[1] : SSet.{u}) ⟶ beadSpace m dim :=
  Pi.lift (beadEdgeComponent m dim a b hab)

theorem beadEdgeMap_π (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (i : Fin m) :
    beadEdgeMap m dim a b hab ≫
      Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i =
        beadEdgeComponent m dim a b hab i :=
  Pi.lift_π _ i

theorem beadEdgeMap_first (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    (beadEdgeMap m dim a b hab).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = a := by
  apply beadVertex_ext m dim
  intro i
  have h := congrFun
    (NatTrans.congr_app (beadEdgeMap_π m dim a b hab i) (op ⦋0⦌))
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  change (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _
    ((beadEdgeMap m dim a b hab).app _
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        (beadEdgeComponent m dim a b hab i).app _
          (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) at h
  exact h.trans (beadEdgeComponent_first m dim a b hab i)

theorem beadEdgeMap_last (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    (beadEdgeMap m dim a b hab).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b := by
  apply beadVertex_ext m dim
  intro i
  have h := congrFun
    (NatTrans.congr_app (beadEdgeMap_π m dim a b hab i) (op ⦋0⦌))
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  change (Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _
    ((beadEdgeMap m dim a b hab).app _
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        (beadEdgeComponent m dim a b hab i).app _
          (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) at h
  exact h.trans (beadEdgeComponent_last m dim a b hab i)

theorem singleOne_first :
    (NecklaceCode.singleIso.{u} 1).hom.app (op ⦋0⦌)
      (NecklaceCode.single 1).first =
        SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [NecklaceCode.singleIso_vertex]
  simp [NecklaceCode.first]
  rfl

theorem singleOne_last :
    (NecklaceCode.singleIso.{u} 1).hom.app (op ⦋0⦌)
      (NecklaceCode.single 1).last =
        SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [NecklaceCode.singleIso_vertex]
  simp [NecklaceCode.last, NecklaceCode.single]
  rfl

/-- The unique coordinatewise edge as an actual one-bead necklace over the product. -/
def edgeOver (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    NecklacesOver (beadSpace m dim) a b where
  code := NecklaceCode.single 1
  map := (NecklaceCode.singleIso 1).hom ≫ beadEdgeMap m dim a b hab
  first := by
    change (beadEdgeMap m dim a b hab).app _
      ((NecklaceCode.singleIso 1).hom.app _ (NecklaceCode.single 1).first) = a
    rw [singleOne_first, beadEdgeMap_first]
  last := by
    change (beadEdgeMap m dim a b hab).app _
      ((NecklaceCode.singleIso 1).hom.app _ (NecklaceCode.single 1).last) = b
    rw [singleOne_last, beadEdgeMap_last]

def constantEdgeFunctor (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    NecklacesOver (beadSpace m dim) a b ⥤
      NecklacesOver (beadSpace m dim) a b :=
  (Functor.const _).obj (edgeOver m dim a b hab)

theorem simplex01_hom_ext (n : ℕ)
    (f g : (Δ[1] : SSet.{u}) ⟶ Δ[n])
    (h₀ : f.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      g.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : f.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      g.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) : f = g := by
  apply stdSimplex_hom_ext
  intro x
  let i : Fin 2 := SSet.stdSimplex.obj₀Equiv x
  have hx : x = SSet.stdSimplex.obj₀Equiv.symm i := by
    exact (SSet.stdSimplex.obj₀Equiv.symm_apply_apply x).symm
  rw [hx]
  have hi : i = 0 ∨ i = 1 := by
    by_cases h : i.val = 0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by have hi := i.isLt; omega))
  rcases hi with h | h
  · rw [h]; exact h₀
  · rw [h]; exact h₁

/-- A map from the edge simplex to a product of beads is fixed by both endpoints. -/
theorem beadEdgeMap_unique (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (g : (Δ[1] : SSet.{u}) ⟶ beadSpace m dim)
    (hg₀ : g.app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = a)
    (hg₁ : g.app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b) :
    g = beadEdgeMap m dim a b hab := by
  apply Pi.hom_ext
  intro i
  apply (cancel_mono (NecklaceCode.singleIso (dim i)).hom).1
  apply simplex01_hom_ext (dim i)
  · change (NecklaceCode.singleIso (dim i)).hom.app _
      ((Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _
        (g.app _ (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) =
      (NecklaceCode.singleIso (dim i)).hom.app _
        ((Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _
          ((beadEdgeMap m dim a b hab).app _
            (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    rw [hg₀, beadEdgeMap_first]
  · change (NecklaceCode.singleIso (dim i)).hom.app _
      ((Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _
        (g.app _ (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) =
      (NecklaceCode.singleIso (dim i)).hom.app _
        ((Pi.π (fun j : Fin m ↦ (NecklaceCode.single (dim j)).toSSet) i).app _
          ((beadEdgeMap m dim a b hab).app _
            (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    rw [hg₁, beadEdgeMap_last]

end

end DaggerOriginalProductGadget
