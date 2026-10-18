import NativeOriginalEC2RealizationUnitComparison
import NativeOriginalActionCanonicalConstants
import OriginalCompletedDaggerDerivedMapping

/-! The exact enriched constants map to the SAME old canonical constants on components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerOriginalCompletedDaggerDerivedMapping
open DaggerNativeOriginalC2RealizationMapping DaggerNativeOriginalActionCanonicalConstants
open DaggerNativeOriginalEC2RealizationUnitComparison
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u
namespace DaggerNativeOriginalEC2CanonicalComponents
noncomputable section

def zeroAction : Action SSet.{u} C2.{u} := Action.trivial C2.{u} (Δ[0] : SSet.{u})
def zeroVertex : zeroAction.{u}.V _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)

theorem zero_fixed (g : C2.{u}) :
    (zeroAction.ρ g).asHom.app (op ⦋0⦌) zeroVertex = zeroVertex := rfl

def fixedVertexMap (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x) : zeroAction ⟶ A where
  hom := SSet.yonedaEquiv.symm x
  comm g := by
    change 𝟙 _ ≫ SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm x ≫ (A.ρ g).asHom
    rw [Category.id_comp, SSet.yonedaEquiv_symm_comp, hx]

theorem fixedVertexMap_zero (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x) :
    (fixedVertexMap A x hx).hom.app (op ⦋0⦌) zeroVertex = x := by
  change (SSet.yonedaEquiv.symm x).app (op ⦋0⦌) zeroVertex = x
  rw [SSet.yonedaEquiv_symm_zero]
  simp only [SSet.const_app]
  rw [show SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ from Subsingleton.elim _ _]
  exact congrFun (A.V.map_id _) x

def zeroEnrichedVertex : (enrichedMapping simplicialAction zeroAction.{u}) _⦋0⦌ where
  hom := SSet.stdSimplex.objZeroIsTerminal.from _
  comm _g := SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _

instance zero_enriched_vertices_subsingleton :
    Subsingleton ((enrichedMapping simplicialAction zeroAction.{u}) _⦋0⦌) :=
  ⟨fun f g ↦ by
    apply Action.hom_ext
    exact SSet.stdSimplex.objZeroIsTerminal.hom_ext f.hom g.hom⟩

instance zero_enriched_components_subsingleton :
    Subsingleton (enrichedMapping simplicialAction zeroAction.{u}).π₀ := by
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
  exact congrArg SSet.π₀.mk (Subsingleton.elim a b)

instance zero_kan : zeroAction.{u}.V.KanComplex := by
  change (Δ[0] : SSet.{u}).KanComplex
  infer_instance

instance zero_enriched_kan : (enrichedMapping simplicialAction zeroAction.{u}).KanComplex := by
  have : IsFibrant zeroAction.{u} :=
    (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2
      (inferInstanceAs (IsFibrant (Δ[0] : SSet.{u})))
  exact enrichedMapping_kan simplicialAction zeroAction

instance zero_realized_components_subsingleton :
    Subsingleton (mappingFunctor.obj zeroAction.{u}).π₀ := by
  have h := (SSet.weakEquivalence_iff_kanComplexW (comparison zeroAction.{u})).mp
    (comparison_weak zeroAction)
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := h.bijective_mapπ₀.surjective a
  obtain ⟨b, rfl⟩ := h.bijective_mapπ₀.surjective b
  exact congrArg (SSet.mapπ₀ (comparison zeroAction)) (Subsingleton.elim a b)

def enrichedConstant (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x) :
    (enrichedMapping simplicialAction A) _⦋0⦌ :=
  (enrichedMappingMap simplicialAction (fixedVertexMap A x hx)).app (op ⦋0⦌)
    zeroEnrichedVertex

theorem enrichedConstant_hom (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x) :
    (enrichedConstant A x hx).hom = SSet.const x := by
  change zeroEnrichedVertex.hom ≫ SSet.yonedaEquiv.symm x = SSet.const x
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]

theorem comparison_constant_component (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x) :
    SSet.mapπ₀ (comparison A) (SSet.π₀.mk (enrichedConstant A x hx)) =
      SSet.π₀.mk (canonicalZero A x hx) := by
  let f := fixedVertexMap A x hx
  have hn := congrFun (NatTrans.congr_app (comparison_naturality f) (op ⦋0⦌))
    zeroEnrichedVertex
  change (comparison A).app (op ⦋0⦌) (enrichedConstant A x hx) =
    (mappingFunctor.map f).app (op ⦋0⦌)
      ((comparison zeroAction).app (op ⦋0⦌) zeroEnrichedVertex) at hn
  have hz : SSet.π₀.mk ((comparison zeroAction).app (op ⦋0⦌) zeroEnrichedVertex) =
      SSet.π₀.mk (canonicalZero zeroAction zeroVertex zero_fixed) := Subsingleton.elim _ _
  rw [SSet.mapπ₀_mk, hn, ← SSet.mapπ₀_mk, hz, SSet.mapπ₀_mk]
  exact congrArg SSet.π₀.mk
    (canonicalZero_naturality f zeroVertex zero_fixed x hx (fixedVertexMap_zero A x hx))

theorem same_component_iff (A : Action SSet.{u} C2.{u}) [A.V.KanComplex]
    (x y : A.V _⦋0⦌)
    (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x)
    (hy : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) y = y) :
    SSet.π₀.mk (enrichedConstant A x hx) = SSet.π₀.mk (enrichedConstant A y hy) ↔
      SSet.π₀.mk (canonicalZero A x hx) = SSet.π₀.mk (canonicalZero A y hy) := by
  have : IsFibrant A :=
    (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2 inferInstance
  have : (enrichedMapping simplicialAction A).KanComplex := enrichedMapping_kan simplicialAction A
  have h := (SSet.weakEquivalence_iff_kanComplexW (comparison A)).mp (comparison_weak A)
  rw [← comparison_constant_component A x hx, ← comparison_constant_component A y hy]
  exact h.bijective_mapπ₀.injective.eq_iff.symm

end
end DaggerNativeOriginalEC2CanonicalComponents
