import ChosenNecklaceWedgeFlags
import ChosenNecklaceUnitCodeMaps

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

namespace Flag

variable {T : NecklaceCode} {n : ℕ}

def pointFlag (n : ℕ) : Flag.{u} NecklaceCode.point n where
  chain := OrderHom.const _ Set.univ
  joints _ _ := Set.mem_univ _

theorem pointFlag_unique (F : Flag.{u} NecklaceCode.point n) : F = pointFlag n := by
  apply ext
  intro i
  apply Set.eq_univ_of_forall
  intro v
  apply F.chain.monotone (Fin.zero_le i)
  apply F.joints
  change v.down ∈ ({0} : Finset (Fin 1))
  simp only [Finset.mem_singleton]
  apply Fin.ext
  change v.down.val = 0
  have h := v.down.isLt
  change v.down.val < 1 at h
  omega

end Flag

theorem mapVertices_pointAt (T : NecklaceCode) (v : Vertices.{u} T)
    (w : Vertices.{u} NecklaceCode.point) :
    mapVertices (T := NecklaceCode.point) (U := T) (pointAt T v) w = v := by
  dsimp only [mapVertices, pointAt]
  rw [pointAt_vertex_apply, T.verticesEquiv.apply_symm_apply]

namespace Flag

variable {T : NecklaceCode} {n : ℕ}

theorem wedge_left_unit (F : Flag.{u} T n) :
    map (wedgeLeftUnitCode T) (wedge (pointFlag n) F) = F := by
  apply ext
  intro i
  have hl := congrArg mapVertices (wedgeLeftUnit_point.{u} T)
  have hr := congrArg mapVertices (wedgeLeftUnit.{u} T).inv_hom_id
  rw [mapVertices_comp] at hl hr
  change mapVertices (wedgeLeftUnit T).hom ∘
    mapVertices (wedgeιRight NecklaceCode.point T) = mapVertices (𝟙 _) at hr
  change mapVertices (wedgeLeftUnit T).hom ''
      (mapVertices (wedgeιLeft NecklaceCode.point T) '' Set.univ ∪
        mapVertices (wedgeιRight NecklaceCode.point T) '' F.chain i) = F.chain i
  rw [Set.image_union, Set.image_image, Set.image_image]
  change (mapVertices (wedgeLeftUnit T).hom ∘
      mapVertices (wedgeιLeft NecklaceCode.point T)) '' Set.univ ∪
    (mapVertices (wedgeLeftUnit T).hom ∘
      mapVertices (wedgeιRight NecklaceCode.point T)) '' F.chain i = _
  rw [hl, hr, mapVertices_id, Set.image_id]
  apply Set.union_eq_right.mpr
  rintro v ⟨w, _hw, rfl⟩
  rw [mapVertices_pointAt]
  exact F.chain.monotone (Fin.zero_le i) (F.joints _ T.first_mem)

theorem wedge_right_unit (F : Flag.{u} T n) :
    map (wedgeRightUnitCode T) (wedge F (pointFlag n)) = F := by
  apply ext
  intro i
  have hl := congrArg mapVertices (wedgeRightUnit.{u} T).inv_hom_id
  have hr := congrArg mapVertices (wedgeRightUnit_point.{u} T)
  rw [mapVertices_comp] at hl hr
  change mapVertices (wedgeRightUnit T).hom ∘
    mapVertices (wedgeιLeft T NecklaceCode.point) = mapVertices (𝟙 _) at hl
  change mapVertices (wedgeRightUnit T).hom ''
      (mapVertices (wedgeιLeft T NecklaceCode.point) '' F.chain i ∪
        mapVertices (wedgeιRight T NecklaceCode.point) '' Set.univ) = F.chain i
  rw [Set.image_union, Set.image_image, Set.image_image]
  change (mapVertices (wedgeRightUnit T).hom ∘
      mapVertices (wedgeιLeft T NecklaceCode.point)) '' F.chain i ∪
    (mapVertices (wedgeRightUnit T).hom ∘
      mapVertices (wedgeιRight T NecklaceCode.point)) '' Set.univ = _
  rw [hl, hr, mapVertices_id, Set.image_id]
  apply Set.union_eq_left.mpr
  rintro v ⟨w, _hw, rfl⟩
  rw [mapVertices_pointAt]
  exact F.chain.monotone (Fin.zero_le i) (F.joints _ T.last_mem)

end Flag

end

end DaggerChosenRigidificationNecklace.NecklaceCode
