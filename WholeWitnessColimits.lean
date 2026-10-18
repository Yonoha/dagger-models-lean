import WitnessColimitInverse
import InverseTriangleColimitData

/-!
# Whole inverse-witness colimits over the actual original arrow cocone

The original colimit arrow, its actual inverse, and every chosen edge and triangle
are retained. Strict descent gives the full witness-category universal property.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerSimplexInverseWitnessCategory
open DaggerWitnessColimitInverse DaggerInverseTriangleColimitData
universe u v w
namespace DaggerWholeWitnessColimits
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Witness R} {c : Cocone (F ⋙ forget R)}

def leftData (hc : IsColimit c) : Data J where
  diagram := leftDiagram R
  cocone := leftCocone R
  isColimit := leftIsColimit R hc
  source j := R.map (F.obj j).arrow.hom ≫ (F.obj j).data.inv
  target _ := 𝟙 _
  triangles j := (F.obj j).data.left
  compatible := fun {_ _} f ↦ (F.map f).triangleLeft
  sourceMap := R.map c.pt.hom ≫ inverse R hc
  targetMap := 𝟙 _
  source_fac := left_composite_square R hc
  target_fac j := (Category.id_comp (R.map (c.ι.app j).left)).trans
    (Category.comp_id (R.map (c.ι.app j).left)).symm

def rightData (hc : IsColimit c) : Data J where
  diagram := rightDiagram R
  cocone := rightCocone R
  isColimit := rightIsColimit R hc
  source j := (F.obj j).data.inv ≫ R.map (F.obj j).arrow.hom
  target _ := 𝟙 _
  triangles j := (F.obj j).data.right
  compatible := fun {_ _} f ↦ (F.map f).triangleRight
  sourceMap := inverse R hc ≫ R.map c.pt.hom
  targetMap := 𝟙 _
  source_fac := right_composite_square R hc
  target_fac j := (Category.id_comp (R.map (c.ι.app j).right)).trans
    (Category.comp_id (R.map (c.ι.app j).right)).symm

def colimitWitness (hc : IsColimit c) : Witness R :=
  ⟨c.pt, ⟨inverse R hc, Data.colimit (J := J) (leftData R hc),
    Data.colimit (J := J) (rightData R hc)⟩⟩

def leg (hc : IsColimit c) (j : J) : F.obj j ⟶ colimitWitness R hc where
  square := c.ι.app j
  inverse_commutes := inverse_fac R hc j
  triangleLeft := Data.leg_square (J := J) (leftData R hc) j
  triangleRight := Data.leg_square (J := J) (rightData R hc) j

def liftedCocone (hc : IsColimit c) : Cocone F where
  pt := colimitWitness R hc
  ι :=
    { app := leg R hc
      naturality := fun _ _ f ↦ Hom.ext R (c.ι.naturality f) }

def desc (hc : IsColimit c) (s : Cocone F) : colimitWitness R hc ⟶ s.pt where
  square := hc.desc ((forget R).mapCocone s)
  inverse_commutes := by
    apply inverse_target_square R hc s.pt
    intro j
    rw [hc.fac ((forget R).mapCocone s) j]
    exact (s.ι.app j).inverse_commutes
  triangleLeft := by
    apply Data.target_square (J := J) (leftData R hc)
    intro j
    change TriangleSquare
      (R.map (c.ι.app j).left ≫ R.map (hc.desc ((forget R).mapCocone s)).left)
      (F.obj j).data.left s.pt.data.left
    rw [← R.map_comp]
    have hj := congrArg
      (fun t : (F.obj j).arrow ⟶ s.pt.arrow ↦ t.left)
      (hc.fac ((forget R).mapCocone s) j)
    change (c.ι.app j).left ≫ (hc.desc ((forget R).mapCocone s)).left =
      (s.ι.app j).square.left at hj
    rw [hj]
    exact (s.ι.app j).triangleLeft
  triangleRight := by
    apply Data.target_square (J := J) (rightData R hc)
    intro j
    change TriangleSquare
      (R.map (c.ι.app j).right ≫ R.map (hc.desc ((forget R).mapCocone s)).right)
      (F.obj j).data.right s.pt.data.right
    rw [← R.map_comp]
    have hj := congrArg
      (fun t : (F.obj j).arrow ⟶ s.pt.arrow ↦ t.right)
      (hc.fac ((forget R).mapCocone s) j)
    change (c.ι.app j).right ≫ (hc.desc ((forget R).mapCocone s)).right =
      (s.ι.app j).square.right at hj
    rw [hj]
    exact (s.ι.app j).triangleRight

def liftedIsColimit (hc : IsColimit c) : IsColimit (liftedCocone R hc) where
  desc := desc R hc
  fac s j := Hom.ext R (hc.fac ((forget R).mapCocone s) j)
  uniq s m h := by
    apply Hom.ext R
    apply hc.uniq ((forget R).mapCocone s) m.square
    intro j
    exact congrArg (fun f : F.obj j ⟶ s.pt ↦ f.square) (h j)

instance witnessHasColimits : HasColimitsOfShape J (Witness R) where
  has_colimit F := ⟨⟨liftedCocone R (colimit.isColimit (F ⋙ forget R)),
    liftedIsColimit R (colimit.isColimit (F ⋙ forget R))⟩⟩

instance forgetPreservesColimits : PreservesColimitsOfShape J (forget R) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (liftedIsColimit R (colimit.isColimit (F ⋙ forget R)))
    (colimit.isColimit (F ⋙ forget R))

end
end DaggerWholeWitnessColimits
