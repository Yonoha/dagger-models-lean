import OriginalProductBeadEdge

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalProductGadget

noncomputable section

open DaggerChosenRigidificationNecklace

theorem inclusion_first_std (T : NecklaceCode) :
    T.inclusion.app (op ⦋0⦌) T.first =
      SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (T.len + 1)) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [← T.verticesEquiv_down]
  simp [NecklaceCode.first]
  rfl

theorem inclusion_last_std (T : NecklaceCode) :
    T.inclusion.app (op ⦋0⦌) T.last =
      SSet.stdSimplex.obj₀Equiv.symm (Fin.last T.len) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [← T.verticesEquiv_down]
  simp [NecklaceCode.last]
  rfl

theorem completionExtension_first (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    (P : NecklacesOver (beadSpace m dim) a b) :
    (beadProductExtension P.code m dim P.map).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (P.code.len + 1))) = a := by
  have h := congrFun
    (NatTrans.congr_app (beadProductExtension_fac P.code m dim P.map) (op ⦋0⦌))
    P.code.first
  change (beadProductExtension P.code m dim P.map).app _
    (P.code.inclusion.app _ P.code.first) = P.map.app _ P.code.first at h
  rw [inclusion_first_std] at h
  exact h.trans P.first

theorem completionExtension_last (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    (P : NecklacesOver (beadSpace m dim) a b) :
    (beadProductExtension P.code m dim P.map).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (Fin.last P.code.len)) = b := by
  have h := congrFun
    (NatTrans.congr_app (beadProductExtension_fac P.code m dim P.map) (op ⦋0⦌))
    P.code.last
  change (beadProductExtension P.code m dim P.map).app _
    (P.code.inclusion.app _ P.code.last) = P.map.app _ P.code.last at h
  rw [inclusion_last_std] at h
  exact h.trans P.last

def edgeToAmbient (T : NecklaceCode) : (Δ[1] : SSet.{u}) ⟶
    (Δ[T.len] : SSet.{u}) :=
  simplexEdge.{u} T.len 0 (Fin.last T.len) (Fin.zero_le _)

theorem edgeToAmbient_first (T : NecklaceCode) :
    (edgeToAmbient T).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
        SSet.stdSimplex.obj₀Equiv.{u}.symm (0 : Fin (T.len + 1)) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  exact simplexEdge_first.{u} T.len 0 (Fin.last T.len) (Fin.zero_le _)

theorem edgeToAmbient_last (T : NecklaceCode) :
    (edgeToAmbient T).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) =
        SSet.stdSimplex.obj₀Equiv.{u}.symm (Fin.last T.len) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  exact simplexEdge_last.{u} T.len 0 (Fin.last T.len) (Fin.zero_le _)

theorem edgeToAmbient_naturality {T U : NecklaceCode}
    (h : NecklaceCode.Hom.{u} T U) :
    edgeToAmbient T ≫ ambientSimplexMap h.map = edgeToAmbient U := by
  apply simplex01_hom_ext U.len
  · change (ambientSimplexMap h.map).app _
      ((edgeToAmbient T).app _
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        (edgeToAmbient U).app _
          (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    rw [edgeToAmbient_first, ← inclusion_first_std,
      ambientSimplexMap_first h, inclusion_first_std, edgeToAmbient_first]
  · change (ambientSimplexMap h.map).app _
      ((edgeToAmbient T).app _
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        (edgeToAmbient U).app _
          (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    rw [edgeToAmbient_last, ← inclusion_last_std,
      ambientSimplexMap_last h, inclusion_last_std, edgeToAmbient_last]

theorem edgeToCompletion_product (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (P : NecklacesOver (beadSpace m dim) a b) :
    edgeToAmbient P.code ≫ beadProductExtension P.code m dim P.map =
      beadEdgeMap m dim a b hab := by
  apply beadEdgeMap_unique m dim a b hab
  · change (beadProductExtension P.code m dim P.map).app _
      ((edgeToAmbient P.code).app _
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = a
    rw [edgeToAmbient_first]
    exact completionExtension_first m dim P
  · change (beadProductExtension P.code m dim P.map).app _
      ((edgeToAmbient P.code).app _
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = b
    rw [edgeToAmbient_last]
    exact completionExtension_last m dim P

/-- The fixed edge maps to each completed necklace over the original product. -/
def edgeToCompletion (m : ℕ) (dim : Fin m → ℕ)
    {a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)}
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b)
    (P : NecklacesOver (beadSpace m dim) a b) :
    edgeOver m dim a b hab ⟶ completeObject m dim P where
  hom :=
    { map := (NecklaceCode.singleIso 1).hom ≫ edgeToAmbient P.code ≫
        (NecklaceCode.singleIso P.code.len).inv
      first := by
        change (NecklaceCode.singleIso P.code.len).inv.app _
          ((edgeToAmbient P.code).app _
            ((NecklaceCode.singleIso 1).hom.app _
              (NecklaceCode.single 1).first)) =
                (NecklaceCode.single P.code.len).first
        rw [singleOne_first, edgeToAmbient_first]
        have h := (toComplete m dim P).hom.first
        change (NecklaceCode.singleIso P.code.len).inv.app _
          (P.code.inclusion.app _ P.code.first) =
            (NecklaceCode.single P.code.len).first at h
        rwa [inclusion_first_std] at h
      last := by
        change (NecklaceCode.singleIso P.code.len).inv.app _
          ((edgeToAmbient P.code).app _
            ((NecklaceCode.singleIso 1).hom.app _
              (NecklaceCode.single 1).last)) =
                (NecklaceCode.single P.code.len).last
        rw [singleOne_last, edgeToAmbient_last]
        have h := (toComplete m dim P).hom.last
        change (NecklaceCode.singleIso P.code.len).inv.app _
          (P.code.inclusion.app _ P.code.last) =
            (NecklaceCode.single P.code.len).last at h
        rwa [inclusion_last_std] at h }
  w := by
    change ((NecklaceCode.singleIso 1).hom ≫ edgeToAmbient P.code ≫
      (NecklaceCode.singleIso P.code.len).inv) ≫
        ((NecklaceCode.singleIso P.code.len).hom ≫
          beadProductExtension P.code m dim P.map) =
            (NecklaceCode.singleIso 1).hom ≫ beadEdgeMap m dim a b hab
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [edgeToCompletion_product m dim hab P]

/-- The fixed endpoint edge maps naturally to every ambient completion. -/
def constantToCompletionNat (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    constantEdgeFunctor m dim a b hab ⟶ completionFunctor m dim a b where
  app := edgeToCompletion m dim hab
  naturality := by
    intro P Q h
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 ((NecklaceCode.single 1).toSSet : SSet.{u}) ≫
      ((NecklaceCode.singleIso 1).hom ≫ edgeToAmbient Q.code ≫
        (NecklaceCode.singleIso Q.code.len).inv) =
      ((NecklaceCode.singleIso 1).hom ≫ edgeToAmbient P.code ≫
        (NecklaceCode.singleIso P.code.len).inv) ≫
          ((NecklaceCode.singleIso P.code.len).hom ≫
            ambientSimplexMap h.hom.map ≫
            (NecklaceCode.singleIso Q.code.len).inv)
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← edgeToAmbient_naturality h.hom]
    simp only [Category.assoc]

end

end DaggerOriginalProductGadget
