import NativeOriginalC2InvolutionAction
import DaggerModels.SimplicialCat

/-! Whole functors and natural transformations act on involutions using the ORIGINAL C2. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action
universe u
namespace DaggerNativeOriginalFunctorInvolutionAction
noncomputable section

/-- The endomorphism is exactly the original functor image. -/
def imageEnd (T : SimplicialCat.{u, u} ⥤ SSet.{u}) {C : SimplicialCat.{u, u}}
    (F : C ⟶ C) : End (T.obj C) := End.of (T.map F)

/-- The whole original involution equation survives the same functor. -/
theorem image_square (T : SimplicialCat.{u, u} ⥤ SSet.{u}) {C : SimplicialCat.{u, u}}
    (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) : imageEnd T F * imageEnd T F = 1 := by
  change T.map F ≫ T.map F = 𝟙 (T.obj C)
  rw [← T.map_comp, hF, T.map_id]

/-- No replacement of the original group or its generator is used. -/
def actionOf (T : SimplicialCat.{u, u} ⥤ SSet.{u}) {C : SimplicialCat.{u, u}}
    (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalC2InvolutionAction.action (imageEnd T F) (image_square T F hF)

/-- Naturality gives a strict equivariant map whose underlying map is the SAME component. -/
def naturalMap {T U : SimplicialCat.{u, u} ⥤ SSet.{u}} (a : T ⟶ U)
    {C : SimplicialCat.{u, u}} (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    actionOf T F hF ⟶ actionOf U F hF :=
  DaggerNativeOriginalC2InvolutionAction.map (imageEnd T F) (image_square T F hF)
    (imageEnd U F) (image_square U F hF) (a.app C) (a.naturality F)

/-- Every original intertwining functor induces its full original equivariant image. -/
def coefficientMap (T : SimplicialCat.{u, u} ⥤ SSet.{u})
    {C D : SimplicialCat.{u, u}} (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (G : D ⟶ D) (hG : G ≫ G = 𝟙 D) (P : C ⟶ D) (hP : F ≫ P = P ≫ G) :
    actionOf T F hF ⟶ actionOf T G hG :=
  DaggerNativeOriginalC2InvolutionAction.map (imageEnd T F) (image_square T F hF)
    (imageEnd T G) (image_square T G hG) (T.map P) (by
      change T.map F ≫ T.map P = T.map P ≫ T.map G
      rw [← T.map_comp, ← T.map_comp, hP])

/-- The entire component and coefficient square commute as original C2-equivariant maps. -/
theorem naturalMap_naturality {T U : SimplicialCat.{u, u} ⥤ SSet.{u}} (a : T ⟶ U)
    {C D : SimplicialCat.{u, u}} (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (G : D ⟶ D) (hG : G ≫ G = 𝟙 D) (P : C ⟶ D) (hP : F ≫ P = P ≫ G) :
    naturalMap a F hF ≫ coefficientMap U F hF G hG P hP =
      coefficientMap T F hF G hG P hP ≫ naturalMap a G hG := by
  apply Action.hom_ext
  exact (a.naturality P).symm

/-- The original generator acts by the exact original functor image. -/
theorem action_generator (T : SimplicialCat.{u, u} ⥤ SSet.{u}) {C : SimplicialCat.{u, u}}
    (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    ((actionOf T F hF).ρ generator).asHom = T.map F :=
  DaggerNativeOriginalC2InvolutionAction.action_generator (imageEnd T F) (image_square T F hF)

end
end DaggerNativeOriginalFunctorInvolutionAction
