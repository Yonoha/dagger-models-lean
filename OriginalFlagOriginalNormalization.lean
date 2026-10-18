import OriginalFlagSourceAssemblyIso
import OriginalFlagNormalizationTransport

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- SAME original P is the source; the internal assembly iso is now explicitly constructed. -/
def originalNormalization (P : NecklacesOver X a b) : P ⟶ normOver P :=
  normalizationFromAssembly P (sourceAssemblyIso P).symm

theorem originalNormalization_whole (P : NecklacesOver X a b) :
    (originalNormalization P).hom.map =
      (sourceAssemblyIso P).inv.hom.map ≫ (assembledNormalization P).hom.map := rfl

theorem originalNormalization_triangle (P : NecklacesOver X a b) :
    (originalNormalization P).hom.map ≫ (normOver P).map = P.map :=
  (originalNormalization P).w

theorem originalNormalization_first (P : NecklacesOver X a b) :
    (originalNormalization P).hom.map.app (op ⦋0⦌) P.code.first =
      (normOver P).code.first := (originalNormalization P).hom.first

theorem originalNormalization_last (P : NecklacesOver X a b) :
    (originalNormalization P).hom.map.app (op ⦋0⦌) P.code.last =
      (normOver P).code.last := (originalNormalization P).hom.last

theorem originalNormalization_surjective (P : NecklacesOver X a b) :
    Function.Surjective (mapVertices (originalNormalization P).hom.map) :=
  normalizationFromAssembly_surjective P (sourceAssemblyIso P).symm

theorem originalNormalization_operator (P : NecklacesOver X a b)
    {s t : SimplexCategoryᵒᵖ} (α : s ⟶ t) :
    P.code.toSSet.map α ≫ (originalNormalization P).hom.map.app t =
      (originalNormalization P).hom.map.app s ≫ (normOver P).code.toSSet.map α :=
  (originalNormalization P).hom.map.naturality α

def originalNormalizedFlag (P : NecklacesOver X a b) {n : ℕ} (F : Flag.{u} P.code n) :
    Flag.{u} (normOver P).code n := NecklaceCode.Flag.map (originalNormalization P).hom F

theorem originalNormalizedFlag_chain (P : NecklacesOver X a b) {n : ℕ}
    (F : Flag.{u} P.code n) (i : Fin (n + 1)) :
    (originalNormalizedFlag P F).chain i =
      (mapVertices (originalNormalization P).hom.map) '' F.chain i := rfl

/-- The dimension-zero transport uses the literal point and its same original vertex. -/
theorem pointCodeTransport_first (T : NecklaceCode) (h : T = NecklaceCode.point) :
    (eqToHom (congrArg NecklaceCode.toSSet h.symm)).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm 0) = T.first := by
  subst T
  change SSet.stdSimplex.obj₀Equiv.symm 0 = NecklaceCode.point.first
  exact (zeroSimplex_unique _).trans (zeroSimplex_unique _).symm

theorem normOver_all_zero_same_vertex (P : NecklacesOver X a b)
    (hz : ∀ i : Fin (beadCount P.code), (normalizeBead P (jointBead P.code i)).dim = 0) :
    eqToHom (congrArg NecklaceCode.toSSet (normOver_all_zero_code P hz).symm) ≫
      (normOver P).map = SSet.yonedaEquiv.symm (vertexImage P 0) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv.apply_symm_apply]
  rw [SSet.yonedaEquiv_comp]
  have h0 : SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) =
      SSet.stdSimplex.obj₀Equiv.symm 0 :=
    (zeroSimplex_unique _).trans (zeroSimplex_unique _).symm
  have he := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u}))
    (eqToHom (congrArg NecklaceCode.toSSet (normOver_all_zero_code P hz).symm))
  rw [Category.id_comp, h0,
    pointCodeTransport_first (normOver P).code (normOver_all_zero_code P hz)] at he
  rw [he, (normOver P).first, vertexImage_first]

end

end DaggerOriginalFlagFlankification
