import ColimitEndomorphismIsoTriangles

/-!
# Package the proved whole inverse-triangle colimit construction

Every field is actual diagram or colimit data; no model, weak-class rank,
or accessibility conclusion is assumed in the package.
-/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeIhomHoObjects DaggerNativeHoIsoTriangles
open DaggerSimplexInverseWitnessCategory DaggerColimitEndomorphismIsoTriangles
universe u
namespace DaggerInverseTriangleColimitData
noncomputable section
variable (J : Type u) [SmallCategory J]

structure Data where
  diagram : J ⥤ SSet.{u}
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  source : ∀ j, diagram.obj j ⟶ diagram.obj j
  target : ∀ j, diagram.obj j ⟶ diagram.obj j
  triangles : ∀ j, IsoTriangles ((ihom (diagram.obj j)).obj (diagram.obj j))
    (homObject (source j)) (homObject (target j))
  compatible : ∀ {i j} (f : i ⟶ j), TriangleSquare (diagram.map f) (triangles i) (triangles j)
  sourceMap : cocone.pt ⟶ cocone.pt
  targetMap : cocone.pt ⟶ cocone.pt
  source_fac : ∀ j, source j ≫ cocone.ι.app j = cocone.ι.app j ≫ sourceMap
  target_fac : ∀ j, target j ≫ cocone.ι.app j = cocone.ι.app j ≫ targetMap

def Data.colimit (p : Data J) :
    IsoTriangles ((ihom p.cocone.pt).obj p.cocone.pt)
      (homObject p.sourceMap) (homObject p.targetMap) :=
  colimitTriangles p.source p.target p.triangles p.compatible p.isColimit
    p.sourceMap p.targetMap p.source_fac p.target_fac

theorem Data.leg_square (p : Data J) (j : J) :
    TriangleSquare (p.cocone.ι.app j) (p.triangles j) p.colimit :=
  colimitTriangles_leg_square p.source p.target p.triangles p.compatible p.isColimit
    p.sourceMap p.targetMap p.source_fac p.target_fac j

theorem Data.target_square (p : Data J) {Z : SSet.{u}} (a : p.cocone.pt ⟶ Z)
    {z₀ z₁ : SSet.hoFunctor.obj ((ihom Z).obj Z)}
    (e : IsoTriangles ((ihom Z).obj Z) z₀ z₁)
    (ha : ∀ j, TriangleSquare (p.cocone.ι.app j ≫ a) (p.triangles j) e) :
    TriangleSquare a p.colimit e :=
  colimitTriangles_target_square p.source p.target p.triangles p.compatible p.isColimit
    p.sourceMap p.targetMap p.source_fac p.target_fac a e ha

end
end DaggerInverseTriangleColimitData
