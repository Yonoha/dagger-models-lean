import OriginalLeftMappingPiZeroHom

/-!
# Functoriality of actual original coslices and left mapping spaces

Postcomposition of original joined simplices restricts to the exact prefix fiber.
The native mapFiber construction gives the induced map of the strict suffix
fibers. The component-to-Hom comparison commutes with this actual simplicial map
and the original native homotopy functor.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingVertices
open DaggerOriginalLeftMappingPiZeroHom

universe u

namespace DaggerOriginalLeftMappingFunctoriality

noncomputable section

/-- Postcomposition on original joined simplices with the exact mapped prefix. -/
def cosliceMap {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory) (x : X.obj (op k)) :
    simplexCoslice k X x ⟶ simplexCoslice k Y (f.app (op k) x) where
  app n s := ⟨f.app (op ((ordinalJoinLeft k).obj n.unop)) s.val, by
    change Y.map (AugmentedSimplexCategory.inl' k n.unop).op
      (f.app _ s.val) = f.app (op k) x
    have hn := congrFun (f.naturality (AugmentedSimplexCategory.inl' k n.unop).op) s.val
    change f.app (op k) (X.map (AugmentedSimplexCategory.inl' k n.unop).op s.val) =
      Y.map (AugmentedSimplexCategory.inl' k n.unop).op (f.app _ s.val) at hn
    rw [← hn, s.property]⟩
  naturality a b φ := by
    funext s
    apply Subtype.ext
    exact congrFun (f.naturality ((ordinalJoinLeft k).map φ.unop).op) s.val

/-- The actual coslice maps commute with the same original suffix projections. -/
theorem cosliceMap_projection {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory)
    (x : X.obj (op k)) :
    cosliceMap f k x ≫ cosliceProjection k Y (f.app (op k) x) =
      cosliceProjection k X x ≫ f := by
  ext n s
  exact (congrFun (f.naturality (AugmentedSimplexCategory.inr' k n.unop).op) s.val).symm

/-- The induced map of the actual strict left mapping spaces, with mapped original endpoints. -/
def leftMappingMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X.obj (op ⦋0⦌)) :
    leftMappingSpace X x y ⟶ leftMappingSpace Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) :=
  SSet.Subcomplex.mapFiber (cosliceProjection ⦋0⦌ X x)
    (cosliceProjection ⦋0⦌ Y (f.app (op ⦋0⦌) x)) (cosliceMap f ⦋0⦌ x) f
    (cosliceMap_projection f ⦋0⦌ x) y (f.app (op ⦋0⦌) y) rfl

/-- The native fiber map commutes with both exact fiber inclusions. -/
theorem leftMappingMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X.obj (op ⦋0⦌)) :
    leftMappingMap f x y ≫
        (leftMappingSubcomplex Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).ι =
      (leftMappingSubcomplex X x y).ι ≫ cosliceMap f ⦋0⦌ x :=
  SSet.Subcomplex.mapFiber_ι _ _ _ _ _ _ _ _

/-- On actual vertices, the induced mapping-space map is the original mapped edge. -/
theorem vertexEdge_map {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X.obj (op ⦋0⦌))
    (v : (leftMappingSpace X x y).obj (op ⦋0⦌)) :
    vertexEdge Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)
        ((leftMappingMap f x y).app (op ⦋0⦌) v) = (vertexEdge X x y v).map f :=
  SSet.Edge.ext rfl

/-- The actual component comparison commutes with the original native homotopy functor. -/
theorem piZeroToHom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X.obj (op ⦋0⦌))
    (c : (leftMappingSpace X x y).π₀) :
    piZeroToHom Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)
        (SSet.mapπ₀ (leftMappingMap f x y) c) =
      (SSet.hoFunctor.map f).toFunctor.map (piZeroToHom X x y c) := by
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective c
  rw [SSet.mapπ₀_mk, piZeroToHom_mk, piZeroToHom_mk]
  change SSet.Truncated.HomotopyCategory.homMk
      (vertexEdge Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)
        ((leftMappingMap f x y).app (op ⦋0⦌) v)) =
    SSet.Truncated.HomotopyCategory.homMk ((vertexEdge X x y v).map f)
  rw [vertexEdge_map]

end

end DaggerOriginalLeftMappingFunctoriality
