import WholeWitnessColimits

/-! Both original endpoint diagrams and their complete triangle witnesses. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
open DaggerSimplexInverseWitnessCategory DaggerNativeHoIsoTriangles
open DaggerNativeIhomHoObjects
universe u v w
namespace DaggerWholeWitnessSides
noncomputable section
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

def side (X : Witness R) (b : Bool) : SSet.{u} :=
  match b with
  | false => R.obj X.arrow.left
  | true => R.obj X.arrow.right

def sideMap {X Y : Witness R} (a : X.arrow ⟶ Y.arrow) (b : Bool) :
    side R X b ⟶ side R Y b :=
  match b with
  | false => R.map a.left
  | true => R.map a.right

theorem sideMap_comp {X Y Z : Witness R} (a : X.arrow ⟶ Y.arrow) (d : Y.arrow ⟶ Z.arrow)
    (b : Bool) : sideMap R (a ≫ d) b = sideMap R a b ≫ sideMap R d b := by
  cases b <;> exact R.map_comp _ _

def sourceEnd (X : Witness R) (b : Bool) : side R X b ⟶ side R X b :=
  match b with
  | false => R.map X.arrow.hom ≫ X.data.inv
  | true => X.data.inv ≫ R.map X.arrow.hom

def triangles (X : Witness R) (b : Bool) :
    IsoTriangles ((ihom (side R X b)).obj (side R X b))
      (homObject (sourceEnd R X b)) (homObject (𝟙 (side R X b))) :=
  match b with
  | false => X.data.left
  | true => X.data.right

theorem triangleSquare_hom {X Y : Witness R} (f : X ⟶ Y) (b : Bool) :
    TriangleSquare (sideMap R f.square b) (triangles R X b) (triangles R Y b) := by
  cases b
  · exact f.triangleLeft
  · exact f.triangleRight

def sideFunctor (b : Bool) : Witness R ⥤ SSet.{u} where
  obj X := side R X b
  map f := sideMap R f.square b
  map_id X := by cases b <;> exact R.map_id _
  map_comp f g := sideMap_comp R f.square g.square b

variable {J : Type u} [SmallCategory J] [HasColimitsOfShape J C]
  [PreservesColimitsOfShape J R]

instance sideFunctorPreserves (b : Bool) : PreservesColimitsOfShape J (sideFunctor R b) := by
  cases b
  · change PreservesColimitsOfShape J (forget R ⋙ Arrow.leftFunc ⋙ R)
    infer_instance
  · change PreservesColimitsOfShape J (forget R ⋙ Arrow.rightFunc ⋙ R)
    infer_instance

def sideIsColimit {F : J ⥤ Witness R} {c : Cocone F} (hc : IsColimit c) (b : Bool) :
    IsColimit ((sideFunctor R b).mapCocone c) :=
  isColimitOfPreserves (sideFunctor R b) hc

end
end DaggerWholeWitnessSides
