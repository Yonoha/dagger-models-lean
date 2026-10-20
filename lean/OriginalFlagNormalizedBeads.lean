import OriginalFlagJointOrder
import ChosenNecklacesOverWedge

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem singleIso_first (m : ℕ) :
    (singleIso.{u} m).hom.app (op ⦋0⦌) (single m).first =
      SSet.stdSimplex.obj₀Equiv.symm 0 := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [singleIso_vertex.{u}]
  exact congrArg ULift.down ((single m).verticesEquiv.apply_symm_apply (ULift.up 0))

theorem singleIso_last (m : ℕ) :
    (singleIso.{u} m).hom.app (op ⦋0⦌) (single m).last =
      SSet.stdSimplex.obj₀Equiv.symm (Fin.last m) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [singleIso_vertex.{u}]
  exact congrArg ULift.down
    ((single m).verticesEquiv.apply_symm_apply (ULift.up (Fin.last m)))

/-- Actual code map with its full simplicial operator, including m or n equal to zero. -/
def singleOperatorHom {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s] :
    NecklaceCode.Hom.{u} (single m) (single n) where
  map := (singleIso.{u} m).hom ≫ SSet.stdSimplex.map s ≫ (singleIso.{u} n).inv
  first := by
    change (singleIso.{u} n).inv.app _
      ((SSet.stdSimplex.map s).app _ ((singleIso.{u} m).hom.app _ (single m).first)) = _
    rw [singleIso_first.{u}, stdSimplex_map_vertex, simplex_epi_first]
    exact (congrArg ((singleIso.{u} n).inv.app (op ⦋0⦌))
      (singleIso_first.{u} n).symm).trans
        (((singleIso.{u} n).app (op ⦋0⦌)).toEquiv.symm_apply_apply _)
  last := by
    change (singleIso.{u} n).inv.app _
      ((SSet.stdSimplex.map s).app _ ((singleIso.{u} m).hom.app _ (single m).last)) = _
    rw [singleIso_last.{u}, stdSimplex_map_vertex, simplex_epi_last]
    exact (congrArg ((singleIso.{u} n).inv.app (op ⦋0⦌))
      (singleIso_last.{u} n).symm).trans
        (((singleIso.{u} n).app (op ⦋0⦌)).toEquiv.symm_apply_apply _)

theorem singleOperatorHom_iso_triangle {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s] :
    (singleOperatorHom.{u} s).map ≫ (singleIso.{u} n).hom =
      (singleIso.{u} m).hom ≫ SSet.stdSimplex.map s := by
  simp only [singleOperatorHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem singleOperatorHom_vertices {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s]
    (v : Vertices.{u} (single m)) :
    mapVertices (singleOperatorHom.{u} s).map v = ULift.up (s.toOrderHom v.down) := by
  apply ULift.ext
  change ((single n).verticesEquiv
    ((singleOperatorHom.{u} s).map.app _ ((single m).verticesEquiv.symm v))).down = _
  rw [← singleIso_vertex.{u}]
  have h := congrFun (NatTrans.congr_app (singleOperatorHom_iso_triangle s) (op ⦋0⦌))
    ((single m).verticesEquiv.symm v)
  change (singleIso.{u} n).hom.app (op ⦋0⦌)
      ((singleOperatorHom.{u} s).map.app (op ⦋0⦌)
        ((single m).verticesEquiv.symm v)) =
    (SSet.stdSimplex.map s).app (op ⦋0⦌)
      ((singleIso.{u} m).hom.app (op ⦋0⦌) ((single m).verticesEquiv.symm v)) at h
  rw [h]
  change s.toOrderHom (SSet.stdSimplex.obj₀Equiv
    ((singleIso.{u} m).hom.app _ ((single m).verticesEquiv.symm v))) = _
  have hv := singleIso_vertex.{u} m ((single m).verticesEquiv.symm v)
  have hv' : SSet.stdSimplex.obj₀Equiv
      ((singleIso.{u} m).hom.app _ ((single m).verticesEquiv.symm v)) = v.down :=
    hv.trans (congrArg ULift.down ((single m).verticesEquiv.apply_symm_apply v))
  exact congrArg s.toOrderHom hv'

theorem singleOperatorHom_surjective {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) [Epi s] :
    Function.Surjective (mapVertices (singleOperatorHom.{u} s).map) := by
  intro v
  obtain ⟨w, hw⟩ := ((SimplexCategory.epi_iff_surjective (f := s)).mp inferInstance) v.down
  refine ⟨ULift.up w, ?_⟩
  rw [singleOperatorHom_vertices, hw]
  rfl

/-- The original positive bead with its SAME two actual images in X. -/
def sourceBeadOver (P : NecklacesOver X a b) (c : P.code.Bead) :
    NecklacesOver X (vertexImage P c.left) (vertexImage P c.right) where
  code := single c.length
  map := (singleIso.{u} c.length).hom ≫ P.code.beadSimplex c ≫ P.map
  first := by
    change P.map.app _ (P.code.beadSimplex c |>.app _
      ((singleIso.{u} c.length).hom.app _ (single c.length).first)) = _
    rw [singleIso_first.{u}]
    rw [← P.code.verticesEquiv.symm_apply_apply
      (P.code.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm 0)),
      c.beadSimplex_first]
    rfl
  last := by
    change P.map.app _ (P.code.beadSimplex c |>.app _
      ((singleIso.{u} c.length).hom.app _ (single c.length).last)) = _
    rw [singleIso_last.{u}]
    rw [← P.code.verticesEquiv.symm_apply_apply
      (P.code.beadSimplex c |>.app _
        (SSet.stdSimplex.obj₀Equiv.symm (Fin.last c.length))), c.beadSimplex_last]
    rfl

/-- A zero-dimensional decomposition is retained as a literal one-vertex single code. -/
def normalizedBeadOver (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) :
    NecklacesOver X (vertexImage P c.left) (vertexImage P c.right) where
  code := single d.dim
  map := (singleIso.{u} d.dim).hom ≫ SSet.yonedaEquiv.symm d.simplex.val
  first := by
    change (SSet.yonedaEquiv.symm d.simplex.val).app _
      ((singleIso.{u} d.dim).hom.app _ (single d.dim).first) = _
    rw [singleIso_first.{u}]
    exact beadNormalization_first P c d
  last := by
    change (SSet.yonedaEquiv.symm d.simplex.val).app _
      ((singleIso.{u} d.dim).hom.app _ (single d.dim).last) = _
    rw [singleIso_last.{u}]
    exact beadNormalization_last P c d

def normalizedBeadHom (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) :
    sourceBeadOver P c ⟶ normalizedBeadOver P c d := by
  letI := d.epi
  refine ⟨singleOperatorHom.{u} d.operator, ?_⟩
  change ((singleIso.{u} c.length).hom ≫ SSet.stdSimplex.map d.operator ≫
      (singleIso.{u} d.dim).inv) ≫
      ((singleIso.{u} d.dim).hom ≫ SSet.yonedaEquiv.symm d.simplex.val) =
    (singleIso.{u} c.length).hom ≫ P.code.beadSimplex c ≫ P.map
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [beadNormalization_triangle]

theorem normalizedBeadHom_surjective (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) :
    Function.Surjective (mapVertices (normalizedBeadHom P c d).hom.map) := by
  letI := d.epi
  simpa only [normalizedBeadHom] using singleOperatorHom_surjective.{u} d.operator

end

end DaggerOriginalFlagFlankification
