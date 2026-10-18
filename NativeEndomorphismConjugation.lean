import NativeIsoTriangleMaps
import NativeEndomorphismCellSquares

/-! Conjugation transports the actual simplices, with a strict cell square. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed Opposite Simplicial
open DaggerNativeWalkingRetractionMappingEquivalence
open DaggerNativeIhomHoObjects DaggerNativeEndomorphismCellSquares
universe u
namespace DaggerNativeEndomorphismConjugation
noncomputable section

def conjugation {X Y : SSet.{u}} (e : X ≅ Y) : (ihom X).obj X ⟶ (ihom Y).obj Y :=
  (MonoidalClosed.pre e.inv).app X ≫ (ihom Y).map e.hom

theorem conjugation_obj {X Y : SSet.{u}} (e : X ≅ Y) (h : X ⟶ X) :
    (SSet.hoFunctor.map (conjugation e)).toFunctor.obj (homObject h) =
      homObject (e.inv ≫ h ≫ e.hom) := by
  change (postHoFunctor Y e.hom).obj ((preHoFunctor e.inv X).obj (homObject h)) = _
  rw [pre_obj, post_obj]
  rw [Category.assoc]

theorem conjugation_square {X Y : SSet.{u}} (e : X ≅ Y) (n : ℕ)
    (x : ((ihom X).obj X).obj (op ⦋n⦌)) :
    CellSquare e.hom x ((conjugation e).app (op ⦋n⦌) x) := by
  have hm : conjugation e ≫ (MonoidalClosed.pre e.hom).app Y = (ihom X).map e.hom := by
    dsimp [conjugation]
    rw [Category.assoc, (MonoidalClosed.pre e.hom).naturality, ← Category.assoc]
    change ((MonoidalClosed.pre e.inv ≫ MonoidalClosed.pre e.hom).app X) ≫ (ihom X).map e.hom = _
    rw [← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id]
    exact Category.id_comp _
  exact (congrArg (fun f ↦ f.app (op ⦋n⦌) x) hm).symm

end
end DaggerNativeEndomorphismConjugation
