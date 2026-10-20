import OriginalFlagSourcePrefixMaps

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem sourceAssemblyForward_vertices (P : NecklacesOver X a b)
    (v : Vertices.{u} (assembledSource P).code) :
    mapVertices (sourcePrefixForward P (beadCount P.code) le_rfl) v =
      ULift.up (sourceAssemblyOrderIso P v.down) := by
  rw [sourcePrefixForward_vertices]
  exact congrArg ULift.up (Fin.ext rfl)

theorem sourceAssemblyInverse_first (P : NecklacesOver X a b) :
    (sourceAssemblyOrderIso P).symm 0 = 0 := by
  calc
    (sourceAssemblyOrderIso P).symm 0 =
        (sourceAssemblyOrderIso P).symm (sourceAssemblyOrderIso P 0) := by
      rw [sourceAssemblyOrderIso_first]
    _ = 0 := (sourceAssemblyOrderIso P).symm_apply_apply 0

theorem sourceAssemblyInverse_last (P : NecklacesOver X a b) :
    (sourceAssemblyOrderIso P).symm (Fin.last P.code.len) =
      Fin.last (assembledSource P).code.len := by
  calc
    (sourceAssemblyOrderIso P).symm (Fin.last P.code.len) =
        (sourceAssemblyOrderIso P).symm
          (sourceAssemblyOrderIso P (Fin.last (assembledSource P).code.len)) := by
      rw [sourceAssemblyOrderIso_last]
    _ = Fin.last (assembledSource P).code.len := (sourceAssemblyOrderIso P).symm_apply_apply _

theorem sourceAssemblyInverse_beadCondition (P : NecklacesOver X a b) :
    BeadImageCondition (T := P.code) (U := (assembledSource P).code)
      (OrderHomClass.toOrderHom (sourceAssemblyOrderIso P).symm) := by
  intro c
  let e := sourceAssemblyOrderIso P
  have hgap : ∀ v ∈ (assembledSource P).code.joints,
      e.symm c.left < v → v < e.symm c.right → False := by
    intro v hv hl hr
    have hj := (sourceAssembly_joint_iff P v).mp hv
    have hl' := e.strictMono hl
    have hr' := e.strictMono hr
    rw [e.apply_symm_apply] at hl' hr'
    exact c.no_joint (e v) hj hl' hr'
  obtain ⟨d, hd⟩ := interval_in_original_bead (assembledSource P).code
    (e.symm c.left) (e.symm c.right) (e.symm.strictMono c.lt) hgap
  left
  refine ⟨d, ?_⟩
  intro v hv
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact hd _ (Finset.mem_Icc.mpr ⟨e.symm.monotone hl, e.symm.monotone hr⟩)

/-- SAME prefix lift at the full bead count, with both original endpoints. -/
def sourceAssemblyCodeForward (P : NecklacesOver X a b) :
    NecklaceCode.Hom.{u} (assembledSource P).code P.code where
  map := sourcePrefixForward P (beadCount P.code) le_rfl
  first := by
    apply P.code.verticesEquiv.injective
    have h := sourceAssemblyForward_vertices P
      (ULift.up 0 : Vertices.{u} (assembledSource P).code)
    rw [sourceAssemblyOrderIso_first] at h
    simpa only [mapVertices, first, Equiv.apply_symm_apply] using h
  last := by
    apply P.code.verticesEquiv.injective
    have h := sourceAssemblyForward_vertices P
      (ULift.up (Fin.last (assembledSource P).code.len) : Vertices.{u} (assembledSource P).code)
    rw [sourceAssemblyOrderIso_last] at h
    simpa only [mapVertices, last, Equiv.apply_symm_apply] using h

/-- Its inverse is the literal inverse-coordinate orderLift, not a chosen abstract inverse. -/
def sourceAssemblyCodeInverse (P : NecklacesOver X a b) :
    NecklaceCode.Hom.{u} P.code (assembledSource P).code where
  map := orderLift (T := P.code) (U := (assembledSource P).code)
    (OrderHomClass.toOrderHom (sourceAssemblyOrderIso P).symm)
      (sourceAssemblyInverse_beadCondition P)
  first := by
    apply (assembledSource P).code.verticesEquiv.injective
    have h := orderLift_vertices (T := P.code) (U := (assembledSource P).code)
      (OrderHomClass.toOrderHom (sourceAssemblyOrderIso P).symm)
      (sourceAssemblyInverse_beadCondition P)
      (ULift.up 0 : Vertices.{u} P.code)
    change _ = ULift.up ((sourceAssemblyOrderIso P).symm 0) at h
    rw [sourceAssemblyInverse_first] at h
    simpa only [mapVertices, first, Equiv.apply_symm_apply] using h
  last := by
    apply (assembledSource P).code.verticesEquiv.injective
    have h := orderLift_vertices (T := P.code) (U := (assembledSource P).code)
      (OrderHomClass.toOrderHom (sourceAssemblyOrderIso P).symm)
      (sourceAssemblyInverse_beadCondition P)
      (ULift.up (Fin.last P.code.len) : Vertices.{u} P.code)
    change _ = ULift.up ((sourceAssemblyOrderIso P).symm (Fin.last P.code.len)) at h
    rw [sourceAssemblyInverse_last] at h
    simpa only [mapVertices, last, Equiv.apply_symm_apply] using h

theorem sourceAssemblyCodeInverse_vertices (P : NecklacesOver X a b)
    (v : Vertices.{u} P.code) :
    mapVertices (sourceAssemblyCodeInverse P).map v =
      ULift.up ((sourceAssemblyOrderIso P).symm v.down) :=
  orderLift_vertices (T := P.code) (U := (assembledSource P).code)
    (OrderHomClass.toOrderHom (sourceAssemblyOrderIso P).symm)
      (sourceAssemblyInverse_beadCondition P) v

def sourceAssemblyCodeIso (P : NecklacesOver X a b) : (assembledSource P).code ≅ P.code where
  hom := sourceAssemblyCodeForward P
  inv := sourceAssemblyCodeInverse P
  hom_inv_id := by
    apply NecklaceCode.Hom.ext
    apply hom_ext_vertices
    funext v
    change mapVertices ((sourceAssemblyCodeForward P).map ≫
      (sourceAssemblyCodeInverse P).map) v = mapVertices (𝟙 (assembledSource P).code.toSSet) v
    rw [mapVertices_comp, Function.comp_apply, mapVertices_id]
    change mapVertices (sourceAssemblyCodeInverse P).map
      (mapVertices (sourcePrefixForward P (beadCount P.code) le_rfl) v) = v
    rw [sourceAssemblyForward_vertices, sourceAssemblyCodeInverse_vertices]
    apply ULift.ext
    exact (sourceAssemblyOrderIso P).symm_apply_apply v.down
  inv_hom_id := by
    apply NecklaceCode.Hom.ext
    apply hom_ext_vertices
    funext v
    change mapVertices ((sourceAssemblyCodeInverse P).map ≫
      (sourceAssemblyCodeForward P).map) v = mapVertices (𝟙 P.code.toSSet) v
    rw [mapVertices_comp, Function.comp_apply, mapVertices_id]
    change mapVertices (sourcePrefixForward P (beadCount P.code) le_rfl)
      (mapVertices (sourceAssemblyCodeInverse P).map v) = v
    rw [sourceAssemblyCodeInverse_vertices, sourceAssemblyForward_vertices]
    apply ULift.ext
    exact (sourceAssemblyOrderIso P).apply_symm_apply v.down

theorem sourceAssemblyCodeIso_hom_triangle (P : NecklacesOver X a b) :
    (sourceAssemblyCodeIso P).hom.map ≫ P.map = (assembledSource P).map :=
  sourcePrefixForward_triangle P _ _

theorem sourceAssemblyCodeIso_inv_triangle (P : NecklacesOver X a b) :
    (sourceAssemblyCodeIso P).inv.map ≫ (assembledSource P).map = P.map := by
  rw [← sourceAssemblyCodeIso_hom_triangle, ← Category.assoc]
  have h := congrArg (fun f : P.code ⟶ P.code ↦ f.map) (sourceAssemblyCodeIso P).inv_hom_id
  change (sourceAssemblyCodeIso P).inv.map ≫ (sourceAssemblyCodeIso P).hom.map =
    𝟙 (NecklaceCode.toSSet.{u} P.code) at h
  rw [h, Category.id_comp]

/-- The actual folded source is isomorphic over SAME X to the original supplied P. -/
def sourceAssemblyIso (P : NecklacesOver X a b) : assembledSource P ≅ P where
  hom := ⟨(sourceAssemblyCodeIso P).hom, sourceAssemblyCodeIso_hom_triangle P⟩
  inv := ⟨(sourceAssemblyCodeIso P).inv, sourceAssemblyCodeIso_inv_triangle P⟩
  hom_inv_id := NecklacesOver.Hom.ext (sourceAssemblyCodeIso P).hom_inv_id
  inv_hom_id := NecklacesOver.Hom.ext (sourceAssemblyCodeIso P).inv_hom_id

theorem sourceAssemblyIso_hom (P : NecklacesOver X a b) :
    (sourceAssemblyIso P).hom.hom.map = sourcePrefixForward P (beadCount P.code) le_rfl := rfl

theorem sourceAssemblyIso_inv (P : NecklacesOver X a b) :
    (sourceAssemblyIso P).inv.hom.map =
      orderLift (T := P.code) (U := (assembledSource P).code)
        (OrderHomClass.toOrderHom (sourceAssemblyOrderIso P).symm)
      (sourceAssemblyInverse_beadCondition P) := rfl

end

end DaggerOriginalFlagFlankification
