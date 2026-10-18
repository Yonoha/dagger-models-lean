import NativeRealCoherentCotensorComparison

/-! The real comparison is natural for ALL original dagger enriched functors. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseDaggerInvolution
open DaggerNativeBisimplicialDiagonal DaggerNativeRealCoherentCotensorComparison
open DaggerNativeDaggerCotensorResolution
open DaggerNativeCoherentCotensorResolutionNaturality
universe u
namespace DaggerNativeRealCotensorComparisonNaturality
noncomputable section

/-- The same full object-changing cotensor map acts on the dagger parameter diagram. -/
def parameterMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    DaggerNativeDaggerCotensorResolution.parameterDiagram C ⟶
      DaggerNativeDaggerCotensorResolution.parameterDiagram D where
  app n := map (SSet.stdSimplex.obj n.unop) F
  naturality _ _ a := by
    apply DaggerSimplicialCat.Hom.ext
    exact (DaggerNativeCoherentCotensorResolutionNaturality.parameterMap
      F.toEnrichedFunctor).naturality a

/-- The original dagger coherent nerve retains the entire old resolution map. -/
def daggerResolutionMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    DaggerNativeDaggerCotensorResolution.resolution C ⟶
      DaggerNativeDaggerCotensorResolution.resolution D :=
  Functor.whiskerRight (parameterMap F) DaggerNerve.daggerCoherentNerve

/-- Apply outer edgewise to the entire old resolution map. -/
def underlyingMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    underlyingDiagram C ⟶ underlyingDiagram D :=
  Functor.whiskerRight (resolutionMap F.toEnrichedFunctor) edgewise

/-- This square uses the actual original dagger on both cotensors. -/
theorem involution_naturality {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    diagramInvolution C ≫ underlyingMap F = underlyingMap F ≫ diagramInvolution D := by
  apply NatTrans.ext
  funext n
  exact involution_natural ((daggerResolutionMap F).app n)

/-- Every original dagger functor gives a strict real-C2 map on the diagonal resolution. -/
def coefficientMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) : action C ⟶ action D :=
  DaggerNativeOriginalC2InvolutionAction.map
    (diagonalInvolution C) (diagonalInvolution_square C)
    (diagonalInvolution D) (diagonalInvolution_square D)
    (diagonalFunctor.map (underlyingMap F)) (by
      change diagonalFunctor.map (diagramInvolution C) ≫
          diagonalFunctor.map (underlyingMap F) =
        diagonalFunctor.map (underlyingMap F) ≫ diagonalFunctor.map (diagramInvolution D)
      rw [← diagonalFunctor.map_comp, ← diagonalFunctor.map_comp, involution_naturality])

/-- The WHOLE strict equivariant square commutes, including every original object map. -/
theorem comparison_naturality {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    comparisonAction C ≫ coefficientMap F =
      DaggerNativeRealEdgewiseC2Action.map (DaggerNerve.daggerCoherentNerve.map F) ≫
        comparisonAction D := by
  apply Action.hom_ext
  apply NatTrans.ext
  funext n x
  have h := congrArg coherentNerve.map
    (DaggerNativeOriginalCotensorFunctor.constant_natural
      (SSet.stdSimplex.obj n.unop) F.toEnrichedFunctor)
  rw [coherentNerve.map_comp, coherentNerve.map_comp] at h
  exact congrFun (NatTrans.congr_app h
    (DaggerNativeRealEdgewiseIndex.epsilon.op.obj n)) x

end
end DaggerNativeRealCotensorComparisonNaturality
