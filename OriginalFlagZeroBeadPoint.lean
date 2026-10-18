import OriginalFlagOriginalNormalization
import Mathlib.CategoryTheory.EqToHom

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- The zero bead remains at its SAME original two endpoint images. -/
def normalizedBeadZeroPoint (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    NecklacesOver X (vertexImage P c.left) (vertexImage P c.right) where
  code := NecklaceCode.point
  map := SSet.yonedaEquiv.symm (vertexImage P c.left)
  first := pointAt_vertex_apply _ _
  last := (pointAt_vertex_apply _ _).trans (beadNormalization_zero_endpoints P c d h)

theorem normalizedBeadZeroCode_eq (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadOver P c d).code = NecklaceCode.point := by
  apply code_zero_eq_point
  change d.dim = 0
  exact h

def normalizedBeadZeroCodeHom (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    NecklaceCode.Hom.{u} (normalizedBeadOver P c d).code NecklaceCode.point :=
  eqToHom (normalizedBeadZeroCode_eq P c d h)

def normalizedBeadZeroCodeInv (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    NecklaceCode.Hom.{u} NecklaceCode.point (normalizedBeadOver P c d).code :=
  eqToHom (normalizedBeadZeroCode_eq P c d h).symm

theorem normalizedBeadZeroCodeHom_map (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadZeroCodeHom P c d h).map =
      eqToHom (congrArg NecklaceCode.toSSet (normalizedBeadZeroCode_eq P c d h)) :=
  eqToHom_map (NecklaceCode.simplicialFunctor.{u}) _

theorem normalizedBeadZeroCodeInv_map (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadZeroCodeInv P c d h).map =
      eqToHom (congrArg NecklaceCode.toSSet (normalizedBeadZeroCode_eq P c d h).symm) :=
  eqToHom_map (NecklaceCode.simplicialFunctor.{u}) _

theorem normalizedBeadZero_same_vertex (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadZeroCodeInv P c d h).map ≫ (normalizedBeadOver P c d).map =
      SSet.yonedaEquiv.symm (vertexImage P c.left) := by
  rw [normalizedBeadZeroCodeInv_map]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv.apply_symm_apply]
  rw [SSet.yonedaEquiv_comp]
  have h0 : SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) =
      SSet.stdSimplex.obj₀Equiv.symm 0 :=
    (zeroSimplex_unique _).trans (zeroSimplex_unique _).symm
  have he := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u}))
    (eqToHom (congrArg NecklaceCode.toSSet (normalizedBeadZeroCode_eq P c d h).symm))
  rw [Category.id_comp, h0,
    pointCodeTransport_first (normalizedBeadOver P c d).code
      (normalizedBeadZeroCode_eq P c d h)] at he
  rw [he, (normalizedBeadOver P c d).first]

theorem normalizedBeadZero_forward_triangle (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadZeroCodeHom P c d h).map ≫ (normalizedBeadZeroPoint P c d h).map =
      (normalizedBeadOver P c d).map := by
  change (normalizedBeadZeroCodeHom P c d h).map ≫
      SSet.yonedaEquiv.symm (vertexImage P c.left) = _
  rw [← normalizedBeadZero_same_vertex P c d h, ← Category.assoc,
    normalizedBeadZeroCodeHom_map, normalizedBeadZeroCodeInv_map]
  simp

/-- Both inverse arrows retain the actual whole maps into arbitrary original X. -/
def normalizedBeadZeroIso (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    normalizedBeadOver P c d ≅ normalizedBeadZeroPoint P c d h where
  hom := ⟨normalizedBeadZeroCodeHom P c d h,
    normalizedBeadZero_forward_triangle P c d h⟩
  inv := ⟨normalizedBeadZeroCodeInv P c d h, normalizedBeadZero_same_vertex P c d h⟩
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change (normalizedBeadZeroCodeHom P c d h).map ≫
      (normalizedBeadZeroCodeInv P c d h).map = 𝟙 _
    rw [normalizedBeadZeroCodeHom_map, normalizedBeadZeroCodeInv_map]
    simp
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change (normalizedBeadZeroCodeInv P c d h).map ≫
      (normalizedBeadZeroCodeHom P c d h).map = 𝟙 _
    rw [normalizedBeadZeroCodeInv_map, normalizedBeadZeroCodeHom_map]
    simp

theorem normalizedBeadZeroIso_hom (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadZeroIso P c d h).hom.hom.map =
      eqToHom (congrArg NecklaceCode.toSSet (normalizedBeadZeroCode_eq P c d h)) :=
  normalizedBeadZeroCodeHom_map P c d h

theorem normalizedBeadZeroIso_inv (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0) :
    (normalizedBeadZeroIso P c d h).inv.hom.map =
      eqToHom (congrArg NecklaceCode.toSSet (normalizedBeadZeroCode_eq P c d h).symm) :=
  normalizedBeadZeroCodeInv_map P c d h

theorem normalizedBeadZero_operator (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) (h : d.dim = 0)
    {s t : SimplexCategoryᵒᵖ} (α : s ⟶ t) :
    (normalizedBeadOver P c d).code.toSSet.map α ≫
        (normalizedBeadZeroIso P c d h).hom.hom.map.app t =
      (normalizedBeadZeroIso P c d h).hom.hom.map.app s ≫
        NecklaceCode.point.toSSet.map α :=
  (normalizedBeadZeroIso P c d h).hom.hom.map.naturality α

end

end DaggerOriginalFlagFlankification
