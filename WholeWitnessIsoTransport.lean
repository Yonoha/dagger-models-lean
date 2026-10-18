import NativeInverseTriangleIsoTransport
import WholeWitnessSides

/-! A whole inverse witness transports along an original base-arrow isomorphism. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeIhomHoObjects DaggerNativeHoIsoTriangles DaggerSimplexInverseWitnessCategory
open DaggerNativeInverseTriangleIsoTransport DaggerNativeIsoTriangleCellTransport
open DaggerInverseTriangleCellFamily
universe u v w
namespace DaggerWholeWitnessIsoTransport
noncomputable section
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})
  (X : Witness R) {a : Arrow C} (e : X.arrow ≅ a)

abbrev leftIso := R.mapIso (Arrow.leftFunc.mapIso e)
abbrev rightIso := R.mapIso (Arrow.rightFunc.mapIso e)

def inverse : R.obj a.right ⟶ R.obj a.left :=
  (rightIso R X e).inv ≫ X.data.inv ≫ (leftIso R X e).hom

theorem left_conjugated :
    (leftIso R X e).inv ≫ (R.map X.arrow.hom ≫ X.data.inv) ≫ (leftIso R X e).hom =
      R.map a.hom ≫ inverse R X e := by
  have hw := congrArg R.map (Arrow.w e.inv)
  rw [R.map_comp, R.map_comp] at hw
  change R.map e.inv.left ≫ R.map X.arrow.hom = R.map a.hom ≫ R.map e.inv.right at hw
  change R.map e.inv.left ≫ (R.map X.arrow.hom ≫ X.data.inv) ≫ R.map e.hom.left = _
  simpa only [inverse, leftIso, rightIso, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] using congrArg (fun z ↦ z ≫ X.data.inv ≫ R.map e.hom.left) hw

theorem right_conjugated :
    (rightIso R X e).inv ≫ (X.data.inv ≫ R.map X.arrow.hom) ≫ (rightIso R X e).hom =
      inverse R X e ≫ R.map a.hom := by
  have hw := congrArg R.map (Arrow.w e.hom)
  rw [R.map_comp, R.map_comp] at hw
  change R.map e.hom.left ≫ R.map a.hom = R.map X.arrow.hom ≫ R.map e.hom.right at hw
  change R.map e.inv.right ≫ (X.data.inv ≫ R.map X.arrow.hom) ≫ R.map e.hom.right = _
  simpa only [inverse, leftIso, rightIso, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] using congrArg (fun z ↦ R.map e.inv.right ≫ X.data.inv ≫ z) hw.symm

def witness : Witness R where
  arrow := a
  data :=
    { inv := inverse R X e
      left := DaggerNativeIsoTriangleCellTransport.cast
        (congrArg homObject (left_conjugated R X e))
        (congrArg homObject (by simpa only [Category.id_comp] using (leftIso R X e).inv_hom_id :
          (leftIso R X e).inv ≫ 𝟙 _ ≫ (leftIso R X e).hom = 𝟙 _))
        (transport (leftIso R X e) _ _ X.data.left)
      right := DaggerNativeIsoTriangleCellTransport.cast
        (congrArg homObject (right_conjugated R X e))
        (congrArg homObject (by simpa only [Category.id_comp] using (rightIso R X e).inv_hom_id :
          (rightIso R X e).inv ≫ 𝟙 _ ≫ (rightIso R X e).hom = 𝟙 _))
        (transport (rightIso R X e) _ _ X.data.right) }

theorem triangleSquare_cast {A B : SSet.{u}} (f : A ⟶ B)
    {x₀ x₁ : SSet.hoFunctor.obj ((ihom A).obj A)}
    {y₀ y₁ z₀ z₁ : SSet.hoFunctor.obj ((ihom B).obj B)}
    (d : IsoTriangles ((ihom A).obj A) x₀ x₁)
    (t : IsoTriangles ((ihom B).obj B) y₀ y₁) (h₀ : y₀ = z₀) (h₁ : y₁ = z₁)
    (h : TriangleSquare f d t) :
    TriangleSquare f d (DaggerNativeIsoTriangleCellTransport.cast h₀ h₁ t) := by
  apply (square_iff_all_cells _ _ _).2
  intro k
  rw [cell_cast]
  exact (square_iff_all_cells _ _ _).1 h k

def forward : X ⟶ witness R X e where
  square := e.hom
  inverse_commutes := by
    change (rightIso R X e).hom ≫
      ((rightIso R X e).inv ≫ X.data.inv ≫ (leftIso R X e).hom) = _
    exact Iso.hom_inv_id_assoc _ _
  triangleLeft := triangleSquare_cast _ _ _ _ _
    (transport_square (leftIso R X e) _ _ X.data.left)
  triangleRight := triangleSquare_cast _ _ _ _ _
    (transport_square (rightIso R X e) _ _ X.data.right)

end
end DaggerWholeWitnessIsoTransport
