import NativeCoherentResolutionC2Span
import OriginalStrictDaggerGroupoidSigma
import OriginalStrictSimplicialPiZeroGroupoid

/-! Instantiate the SAME strict C2 comparison span with the EXACT original inverse dagger. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerOriginalStrictDaggerGroupoidSigma
open DaggerNativeCoherentResolutionC2Span DaggerNativeCoherentResolutionFunctor
open DaggerNativeOriginalFunctorInvolutionAction DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalStrictSimplicialPiZeroGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalSigmaResolutionSpan
noncomputable section

/-- ALL original dagger functors intertwine the ENTIRE original inverse-dagger functors. -/
theorem sigma_naturality {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (P : C ⟶ D) : strictSigmaFunctor C hC ≫ P.toEnrichedFunctor =
      P.toEnrichedFunctor ≫ strictSigmaFunctor D hD := by
  apply EnrichedFunctor.ext SSet
    (F := strictSigmaFunctor C hC ≫ P.toEnrichedFunctor)
    (G := P.toEnrichedFunctor ≫ strictSigmaFunctor D hD) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact strictSigmaHom_functor hC hD P x y

def coherentSigmaMap (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :=
  coherentMap (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)

def ordinarySigmaMap (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :=
  ordinaryMap (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)

/-- The old actual component groupoid supplies the required input without an extra hypothesis. -/
theorem coherentSigmaMap_weak (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat)
    (hH : ∀ x y : C.Obj, SSet.KanComplex (C.toSimplicialCat.enriched.Hom x y)) :
    WeakEquivalence (coherentSigmaMap C hC).hom :=
  coherentMap_weak _ _ hH
    ⟨strictComponentGroupoid C.toSimplicialCat hC,
      strictComponentGroupoid_category C.toSimplicialCat hC⟩

theorem ordinarySigmaMap_weak (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    WeakEquivalence (ordinarySigmaMap C hC).hom := ordinaryMap_weak _ _

/-- Every original dagger functor gives the SAME functor map on each of the three actions. -/
def sigmaCoefficientMap (T : SimplicialCat.{u, u} ⥤ SSet.{u})
    {C D : DaggerSimplicialCat.{u, u}} (hC : IsStrictGroupoid C.toSimplicialCat)
    (hD : IsStrictGroupoid D.toSimplicialCat) (P : C ⟶ D) :=
  coefficientMap T (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)
    (strictSigmaFunctor D hD) (strictSigmaFunctor_involutive D hD) P.toEnrichedFunctor
    (sigma_naturality hC hD P)

theorem coherentSigmaMap_naturality {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (P : C ⟶ D) :
    coherentSigmaMap C hC ≫ sigmaCoefficientMap diagonalResolutionFunctor hC hD P =
      sigmaCoefficientMap coherentNerve hC hD P ≫ coherentSigmaMap D hD :=
  coherentMap_naturality _ _ _ _ P.toEnrichedFunctor (sigma_naturality hC hD P)

theorem ordinarySigmaMap_naturality {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (P : C ⟶ D) :
    ordinarySigmaMap C hC ≫ sigmaCoefficientMap diagonalResolutionFunctor hC hD P =
      sigmaCoefficientMap diagonalNerveFunctor hC hD P ≫ ordinarySigmaMap D hD :=
  ordinaryMap_naturality _ _ _ _ P.toEnrichedFunctor (sigma_naturality hC hD P)

/-- The ORIGINAL generator fixes each original coherent vertex under actual inverse dagger. -/
theorem coherentSigma_generator_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat)
    (x : (coherentNerve.obj C.toSimplicialCat).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv C.toSimplicialCat
      (((coherentAction (strictSigmaFunctor C hC)
        (strictSigmaFunctor_involutive C hC)).ρ generator).asHom.app (op ⦋0⦌) x) =
          NerveVertices.vertexEquiv C.toSimplicialCat x := by
  rw [action_generator]
  exact DaggerNativeGroupoidalCoherentNerveWeak.vertex_map (strictSigmaFunctor C hC) x

end
end DaggerNativeOriginalSigmaResolutionSpan
