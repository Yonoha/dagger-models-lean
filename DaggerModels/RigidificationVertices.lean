import DaggerModels.NerveVertices

/-!
# Canonical vertices of the original rigidification

The original adjunction unit gives the actual vertex map into the object type.
It is an isomorphism on representables. Colimit preservation and the existing
uniqueness of Yoneda extension give its isomorphism on every simplicial set.
-/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.RigidificationVertices

open NerveVertices

local instance : HasColimits.{u} SimplicialCat.{u, u} := simplicialCatHasColimits
local instance : HasColimitsOfSize.{0, u} SimplicialCat.{u, u} :=
  hasColimitsOfSizeShrink.{0, u} SimplicialCat.{u, u}

/-- The original degree-zero evaluation on simplicial sets. -/
def vertices : SSet.{u} ⥤ Type u :=
  (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)

/-- The actual left-Kan unit, without replacing the chosen rigidification. -/
def thickeningUnit : cosimplicialThickening.{u} ⟶ uliftYoneda.{u} ⋙ rigidification :=
  uliftYoneda.leftKanExtensionUnit cosimplicialThickening

local instance : rigidification.{u}.IsLeftKanExtension thickeningUnit := by
  unfold rigidification thickeningUnit
  infer_instance

/-- Vertices map to objects by the actual ordinary adjunction unit. -/
def canonicalVertex : vertices.{u} ⟶ rigidification ⋙ SimplicialCat.objects where
  app X x := ((rigidificationCoherentNerveAdjunction.unit.app X).app (op ⦋0⦌) x).down.obj
    zeroObject
  naturality {X Y} f := by
    funext x
    exact congrArg (fun P ↦ P.down.obj zeroObject)
      (congrFun (NatTrans.congr_app
        (rigidificationCoherentNerveAdjunction.unit.naturality f) (op ⦋0⦌)) x)

/-- A vertex of a representable is the corresponding original thickening object. -/
def representableVerticesEquiv (n : SimplexCategory) :
    vertices.obj (uliftYoneda.{u}.obj n) ≃ (cosimplicialThickening.obj n).Obj where
  toFun p := .mk ⟨p.down.toOrderHom 0⟩
  invFun i := ⟨SimplexCategory.const ⦋0⦌ n i.as.down⟩
  left_inv p := by
    apply ULift.ext
    exact (SimplexCategory.eq_const_of_zero p.down).symm
  right_inv i := by
    cases i
    rfl

/-- The original representable vertex identification is natural in simplex operators. -/
def representableVerticesIso :
    uliftYoneda.{u} ⋙ vertices ≅ cosimplicialThickening ⋙ SimplicialCat.objects :=
  NatIso.ofComponents (fun n ↦ (representableVerticesEquiv n).toIso) (by
    intro n m f
    funext p
    rfl)

/-- On representables the canonical map is the actual Kan-unit object map. -/
theorem canonicalVertex_simplex (n : SimplexCategory)
    (p : vertices.obj (uliftYoneda.{u}.obj n)) :
    canonicalVertex.app (uliftYoneda.obj n) p =
      (thickeningUnit.app n).obj (representableVerticesEquiv n p) := by
  haveI hKan : rigidification.{u}.IsLeftKanExtension thickeningUnit.{u} := inferInstance
  have hp : uliftYonedaEquiv.{u}.symm p = uliftYoneda.map p.down := by
    apply uliftYonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (uliftYonedaEquiv_uliftYoneda_map p.down).symm
  change (((Presheaf.uliftYonedaAdjunction.{u} rigidification.{u} thickeningUnit.{u}).unit.app
    (uliftYoneda.obj n)).app (op ⦋0⦌) p).down.obj zeroObject = _
  rw [Presheaf.uliftYonedaAdjunction_unit_app_app, hp]
  exact (congrArg (fun k : cosimplicialThickening.obj ⦋0⦌ ⟶
    rigidification.obj (uliftYoneda.obj n) ↦ k.obj zeroObject)
      (thickeningUnit.naturality p.down)).symm

/-- The actual canonical map restricted to representables has an explicit inverse. -/
def representableCanonicalIso :
    uliftYoneda.{u} ⋙ vertices ≅ uliftYoneda ⋙ rigidification ⋙ SimplicialCat.objects :=
  representableVerticesIso ≪≫
    Functor.isoWhiskerRight rigidificationSimplexIso.symm SimplicialCat.objects ≪≫
      Functor.associator _ _ _

theorem representableCanonicalIso_hom :
    representableCanonicalIso.{u}.hom = whiskerLeft uliftYoneda canonicalVertex := by
  ext n p
  exact (canonicalVertex_simplex n p).symm

instance restrictedCanonicalVertexIsIso :
    IsIso (whiskerLeft uliftYoneda.{u} canonicalVertex) := by
  rw [← representableCanonicalIso_hom]
  infer_instance

local instance : PreservesColimitsOfSize.{0, u} vertices.{u} := by
  unfold vertices
  letI : HasColimitsOfSize.{0, u} (Type u) := hasColimitsOfSizeShrink.{0, u} (Type u)
  refine { preservesColimitsOfShape := ?_ }
  intro J hJ
  exact evaluation_preservesColimitsOfShape (C := Type u) (J := J) (op ⦋0⦌)

local instance : PreservesColimitsOfSize.{0, u} rigidification.{u} :=
  rigidificationCoherentNerveAdjunction.leftAdjoint_preservesColimits

local instance : PreservesColimitsOfSize.{0, u} SimplicialCat.objects.{u, u} :=
  SimplicialCat.objectsPreservesColimitsOfSize

/-- The actual unit-based vertex map is invertible on every simplicial set. -/
instance canonicalVertexIsIso : IsIso canonicalVertex.{u} := by
  haveI hF : PreservesColimitsOfSize.{0, u} rigidification.{u} := inferInstance
  haveI hO : PreservesColimitsOfSize.{0, u} SimplicialCat.objects.{u, u} := inferInstance
  haveI hV : PreservesColimitsOfSize.{0, u} vertices.{u} := inferInstance
  haveI hFO : PreservesColimitsOfSize.{0, u}
      (rigidification.{u} ⋙ SimplicialCat.objects) := inferInstance
  letI : (rigidification.{u} ⋙ SimplicialCat.objects).IsLeftKanExtension
      (whiskerLeft uliftYoneda.{u} canonicalVertex.{u}) :=
    (Presheaf.isLeftKanExtension_along_uliftYoneda_iff.{u} _ _).2
      ⟨inferInstance, inferInstance⟩
  letI : vertices.{u}.IsLeftKanExtension (𝟙 (uliftYoneda.{u} ⋙ vertices)) :=
    (Presheaf.isLeftKanExtension_along_uliftYoneda_iff.{u} _ _).2
      ⟨inferInstance, inferInstance⟩
  exact (Functor.isLeftKanExtension_iff_isIso canonicalVertex
    (𝟙 (uliftYoneda.{u} ⋙ vertices)) (whiskerLeft uliftYoneda canonicalVertex)
      (by simp)).1 inferInstance

/-- The natural object identification retains the concrete original adjunction unit. -/
def verticesRigidificationIso : vertices.{u} ≅ rigidification ⋙ SimplicialCat.objects :=
  asIso canonicalVertex

/-- Every original rigidification object is represented by a unique original vertex. -/
def vertexEquiv (X : SSet.{u}) : X.obj (op ⦋0⦌) ≃ (rigidification.obj X).Obj :=
  (verticesRigidificationIso.app X).toEquiv

theorem vertexEquiv_apply (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    vertexEquiv X x =
      ((rigidificationCoherentNerveAdjunction.unit.app X).app (op ⦋0⦌) x).down.obj
        zeroObject := rfl

/-- Every original simplicial map acts naturally under the unit-based identification. -/
theorem vertexEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X.obj (op ⦋0⦌)) :
    (rigidification.map f).obj (vertexEquiv X x) = vertexEquiv Y (f.app (op ⦋0⦌) x) :=
  (congrFun (canonicalVertex.naturality f) x).symm

end DaggerModels.OrdinaryRigidification.RigidificationVertices
