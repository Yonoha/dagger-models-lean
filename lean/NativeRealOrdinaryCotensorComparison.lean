import NativeDaggerDegreeNerveComparison
import NativeRealDaggerDiagramAction
import NativeRealCoherentCotensorComparison
import NativeOrdinaryCoherentResolutionWeak

/-! The SAME original ordinary comparison is a strict real-C2 weak map, for ALL targets. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeBisimplicialDiagonal DaggerNativeRealEdgewiseSSet
open DaggerNativeRealEdgewiseIndex DaggerNativeDaggerDegreeNerveComparison
open DaggerOriginalDaggerRealizationC2Action
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealOrdinaryCotensorComparison
noncomputable section

/-- The strict real action comes from the SAME original degree dagger and nerve reversal. -/
def ordinaryAction (C : DaggerSimplicialCat.{u, u}) : Action SSet.{u} C2.{u} :=
  DaggerNativeRealDaggerDiagramAction.action (degreeDiagram C)

/-- The SAME original ordinary/coherent comparison is now strictly real-equivariant. -/
def comparison (C : DaggerSimplicialCat.{u, u}) :
    ordinaryAction C ⟶ DaggerNativeRealCoherentCotensorComparison.action C :=
  DaggerNativeRealDaggerDiagramAction.map (DaggerNativeDaggerDegreeNerveComparison.comparison C)

/-- Its ENTIRE underlying map is the old comparison with OUTER edgewise before diagonal. -/
theorem comparison_hom (C : DaggerSimplicialCat.{u, u}) :
    (comparison C).hom = diagonalFunctor.map (Functor.whiskerRight
      (DaggerNativeDegreeCotensorComparison.comparison C.toSimplicialCat) edgewise) := rfl

/-- The generator is the original reversed dagger chain, evaluated in the original degree. -/
theorem generator_degree (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    (((ordinaryAction C).ρ generator).asHom).app n =
      (degreeNerve C n).dagger.app (epsilon.op.obj n) := by
  exact congrArg (fun f : End (diagonalFunctor.obj
    (DaggerNativeRealDaggerDiagramAction.underlying (degreeDiagram C))) ↦ f.asHom.app n)
      (DaggerNativeOriginalC2InvolutionAction.action_generator.{u + 1, u, u}
        (DaggerNativeRealDaggerDiagramAction.diagonalInvolution (degreeDiagram C))
        (DaggerNativeRealDaggerDiagramAction.diagonalInvolution_square (degreeDiagram C)))

/-- Reindexing the already proved weak rows at epsilon(n) needs NO target fibrancy input. -/
theorem comparison_weak (C : DaggerSimplicialCat.{u, u}) :
    WeakEquivalence (comparison C).hom := by
  rw [comparison_hom]
  apply DaggerNativeOrdinaryCoherentResolutionWeak.diagonal_weak_of_flipped_rows
  intro n
  exact DaggerNativeOrdinaryCoherentRowFactorization.rowComparison_weak
    C.toSimplicialCat (epsilon.obj n.unop)

end
end DaggerNativeRealOrdinaryCotensorComparison
