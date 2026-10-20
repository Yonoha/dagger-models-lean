import ActualRightConeFinalEdgeMaps

/-! The original cone is the actual pushout of the two-bead weak inclusion. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone DaggerNativeTwoBeadSpineGeometry
open DaggerNativeRightConeFinalEdge DaggerActualRightConeFinalEdgeMaps
universe u
namespace DaggerActualRightConeFinalEdgePushout
noncomputable section

def firstLeg (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ (twoBead n : SSet.{u}) :=
  (firstFaceIso n).hom ≫ SSet.Subcomplex.homOfLE le_sup_left

def lastLeg (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ (twoBead n : SSet.{u}) :=
  (edgeIso n).hom ≫ SSet.Subcomplex.homOfLE le_sup_right

theorem firstLeg_ι (n : ℕ) : firstLeg.{u} n ≫ (twoBead n).ι = face n := by
  rw [firstLeg, Category.assoc, SSet.Subcomplex.homOfLE_ι, firstFaceIso_hom]

theorem lastLeg_ι (n : ℕ) : lastLeg.{u} n ≫ (twoBead n).ι = edgeMap n := by
  rw [lastLeg, Category.assoc, SSet.Subcomplex.homOfLE_ι, edgeIso_hom]

def toEdge (n : ℕ) : (twoBead n : SSet.{u}) ⟶ Δ[1] := (twoBead n).ι ≫ heightMap n

theorem firstLeg_toEdge (n : ℕ) : firstLeg.{u} n ≫ toEdge n =
    collapse n ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  rw [toEdge, ← Category.assoc, firstLeg_ι, face_height]

theorem lastLeg_toEdge (n : ℕ) : lastLeg.{u} n ≫ toEdge n = 𝟙 (Δ[1] : SSet.{u}) := by
  rw [toEdge, ← Category.assoc, lastLeg_ι, edge_height]

theorem square (n : ℕ) : (twoBead.{u} n).ι ≫ simplexIncl n =
    toEdge n ≫ sectionMap n := by
  have sq : SSet.Subcomplex.BicartSq (firstFace.{u} n ⊓ lastEdge n)
      (firstFace n) (lastEdge n) (twoBead n) := ⟨rfl,rfl⟩
  apply sq.isPushout.hom_ext
  · apply (cancel_epi (firstFaceIso n).hom).mp
    change firstLeg n ≫ ((twoBead n).ι ≫ simplexIncl n) =
      firstLeg n ≫ (toEdge n ≫ sectionMap n)
    rw [← Category.assoc, firstLeg_ι, ← Category.assoc, firstLeg_toEdge,
      Category.assoc, first_section]
    exact face_eq_collapse n
  · apply (cancel_epi (edgeIso n).hom).mp
    change lastLeg n ≫ ((twoBead n).ι ≫ simplexIncl n) =
      lastLeg n ≫ (toEdge n ≫ sectionMap n)
    rw [← Category.assoc, lastLeg_ι, ← Category.assoc, lastLeg_toEdge, Category.id_comp]
    rfl

theorem prefix_compat {Z : SSet.{u}} (n : ℕ)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ Z) (h : (Δ[1] : SSet.{u}) ⟶ Z)
    (w : (twoBead n).ι ≫ g = toEdge n ≫ h) :
    face n ≫ g = collapse n ≫ (SSet.stdSimplex.δ (1 : Fin 2) ≫ h) := by
  calc
    face n ≫ g = (firstLeg n ≫ (twoBead n).ι) ≫ g := by rw [firstLeg_ι]
    _ = firstLeg n ≫ ((twoBead n).ι ≫ g) := Category.assoc _ _ _
    _ = firstLeg n ≫ (toEdge n ≫ h) := congrArg (fun f ↦ firstLeg n ≫ f) w
    _ = collapse n ≫ (SSet.stdSimplex.δ (1 : Fin 2) ≫ h) := by
      rw [← Category.assoc, firstLeg_toEdge, Category.assoc]

theorem edge_compat {Z : SSet.{u}} (n : ℕ)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ Z) (h : (Δ[1] : SSet.{u}) ⟶ Z)
    (w : (twoBead n).ι ≫ g = toEdge n ≫ h) : edgeMap n ≫ g = h := by
  calc
    edgeMap n ≫ g = (lastLeg n ≫ (twoBead n).ι) ≫ g := by rw [lastLeg_ι]
    _ = lastLeg n ≫ ((twoBead n).ι ≫ g) := Category.assoc _ _ _
    _ = lastLeg n ≫ (toEdge n ≫ h) := congrArg (fun f ↦ lastLeg n ≫ f) w
    _ = h := by rw [← Category.assoc, lastLeg_toEdge, Category.id_comp]

def quotientDesc {Z : SSet.{u}} (n : ℕ)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ Z) (h : (Δ[1] : SSet.{u}) ⟶ Z)
    (w : (twoBead n).ι ≫ g = toEdge n ≫ h) : cone n ⟶ Z :=
  desc n g (SSet.stdSimplex.δ (1 : Fin 2) ≫ h) (prefix_compat n g h w)

theorem quotientDesc_simplex {Z : SSet.{u}} (n : ℕ)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ Z) (h : (Δ[1] : SSet.{u}) ⟶ Z)
    (w : (twoBead n).ι ≫ g = toEdge n ≫ h) :
    simplexIncl n ≫ quotientDesc n g h w = g := simplexIncl_desc _ _ _ _

theorem quotientDesc_edge {Z : SSet.{u}} (n : ℕ)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ Z) (h : (Δ[1] : SSet.{u}) ⟶ Z)
    (w : (twoBead n).ι ≫ g = toEdge n ≫ h) :
    sectionMap n ≫ quotientDesc n g h w = h := by
  rw [sectionMap, Category.assoc, quotientDesc_simplex]
  exact edge_compat n g h w

theorem quotientDesc_unique {Z : SSet.{u}} (n : ℕ)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ Z) (h : (Δ[1] : SSet.{u}) ⟶ Z)
    (w : (twoBead n).ι ≫ g = toEdge n ≫ h) (k : cone n ⟶ Z)
    (hk0 : simplexIncl n ≫ k = g) (hk1 : sectionMap n ≫ k = h) :
    k = quotientDesc n g h w := by
  apply pushout.hom_ext
  · change simplexIncl n ≫ k = simplexIncl n ≫ quotientDesc n g h w
    rw [quotientDesc_simplex]
    exact hk0
  · change baseIncl n ≫ k = baseIncl n ≫
      desc n g (SSet.stdSimplex.δ (1 : Fin 2) ≫ h) (prefix_compat n g h w)
    rw [baseIncl_desc]
    change alphaMap n ≫ k = _
    rw [← first_section, Category.assoc, hk1]

theorem quotient_isPushout (n : ℕ) :
    IsPushout (twoBead.{u} n).ι (toEdge n) (simplexIncl n) (sectionMap n) := by
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (square n)) ?_
  refine PushoutCocone.IsColimit.mk (square n)
    (fun s ↦ quotientDesc n s.inl s.inr s.condition) ?_ ?_ ?_
  · intro s
    exact quotientDesc_simplex n s.inl s.inr s.condition
  · intro s
    exact quotientDesc_edge n s.inl s.inr s.condition
  · intro s k hk0 hk1
    exact quotientDesc_unique n s.inl s.inr s.condition k hk0 hk1

end
end DaggerActualRightConeFinalEdgePushout
