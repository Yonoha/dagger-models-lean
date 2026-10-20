import DaggerModels.DaggerGraphPresheafForward
import DaggerModels.DaggerGraphPresheafInverse

/-!
# The presheaf counit for dagger simplicial graphs

Reconstructing a graph by endpoint fibers and then taking its total edges
recovers the original presheaf. The counit forgets the endpoint labels and
fiber proofs; its inverse records the two actual endpoints of each edge.
Both maps are natural for every index arrow and every natural transformation,
at the arbitrary common universe `u`.
-/

open CategoryTheory Opposite

universe u

namespace DaggerModels.DaggerGraphPresheaf

open DaggerGraphIndex

/-- Total endpoint fibers recover the vertex and edge values of a presheaf. -/
def counitEquiv (F : Objᵒᵖ ⥤ Type u) (X : Obj) : value (graph F) X ≃ F.obj (op X) :=
  match X with
  | .vertex => Equiv.refl _
  | .edge n =>
      { toFun := fun e ↦ e.2.2.val
        invFun := fun e ↦ ⟨F.map (source n).op e, F.map (target n).op e, ⟨e, rfl, rfl⟩⟩
        left_inv := by
          rintro ⟨x, y, e, hx, hy⟩
          dsimp only at hx hy
          subst x
          subst y
          rfl
        right_inv := fun _ ↦ rfl }

/-- The counit intertwines all ordinary restrictions and the index involution. -/
theorem counitEquiv_pull (F : Objᵒᵖ ⥤ Type u) {X Y : Obj} (f : X ⟶ Y)
    (e : value (graph F) Y) :
    counitEquiv F X (pull (graph F) f e) = F.map f.op (counitEquiv F Y e) := by
  cases X <;> cases Y
  · cases f
    change e = F.map (𝟙 (op Obj.vertex)) e
    exact (FunctorToTypes.map_id_apply F e).symm
  · cases f
    · exact e.2.2.property.1.symm
    · exact e.2.2.property.2.symm
  · cases f
  · rcases f with ⟨α, b⟩
    rename_i n m
    cases b
    · rfl
    · change F.map (swap _).op (F.map (simplex α).op e.2.2.val) =
        F.map (Quiver.Hom.op (V := Obj) (X := .edge n) (Y := .edge m) (α, true)) e.2.2.val
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      change F.map (Quiver.Hom.op (V := Obj) (X := .edge n) (Y := .edge m)
        (𝟙 _ ≫ α, true)) e.2.2.val =
          F.map (Quiver.Hom.op (V := Obj) (X := .edge n) (Y := .edge m) (α, true)) e.2.2.val
      simp

/-- Recovering the presheaf from all endpoint fibers gives an actual presheaf iso. -/
def counitIsoApp (F : Objᵒᵖ ⥤ Type u) : presheaf (graph F) ≅ F :=
  NatIso.ofComponents (fun X ↦ (counitEquiv F X.unop).toIso) (by
    intro X Y f
    funext e
    exact counitEquiv_pull F f.unop e)

@[simp] theorem counitIsoApp_hom_vertex (F : Objᵒᵖ ⥤ Type u)
    (x : F.obj (op Obj.vertex)) : (counitIsoApp F).hom.app (op Obj.vertex) x = x := rfl

@[simp] theorem counitIsoApp_hom_edge (F : Objᵒᵖ ⥤ Type u) (n : SimplexCategory)
    (e : value (graph F) (.edge n)) :
    (counitIsoApp F).hom.app (op (.edge n)) e = e.2.2.val := rfl

@[simp] theorem counitIsoApp_inv_vertex (F : Objᵒᵖ ⥤ Type u)
    (x : F.obj (op Obj.vertex)) : (counitIsoApp F).inv.app (op Obj.vertex) x = x := rfl

@[simp] theorem counitIsoApp_inv_edge (F : Objᵒᵖ ⥤ Type u) (n : SimplexCategory)
    (e : F.obj (op (.edge n))) :
    (counitIsoApp F).inv.app (op (.edge n)) e =
      ⟨F.map (source n).op e, F.map (target n).op e, ⟨e, rfl, rfl⟩⟩ := rfl

/-- The counit's edge projection is natural for arbitrary presheaf maps. -/
theorem counitEquiv_valueMap {F H : Objᵒᵖ ⥤ Type u} (η : F ⟶ H) (X : Obj)
    (e : value (graph F) X) :
    counitEquiv H X (valueMap (graphMap η) X e) =
      η.app (op X) (counitEquiv F X e) := by
  cases X <;> rfl

/-- The natural counit for endpoint-fiber reconstruction and total-edge assembly. -/
def counitIso : inverse.{u} ⋙ functor ≅ 𝟭 (Objᵒᵖ ⥤ Type u) :=
  NatIso.ofComponents counitIsoApp (by
    intro F H η
    ext X e
    exact counitEquiv_valueMap η X.unop e)

@[simp] theorem counitIso_hom_app (F : Objᵒᵖ ⥤ Type u) :
    counitIso.hom.app F = (counitIsoApp F).hom := rfl

@[simp] theorem counitIso_inv_app (F : Objᵒᵖ ⥤ Type u) :
    counitIso.inv.app F = (counitIsoApp F).inv := rfl

end DaggerModels.DaggerGraphPresheaf
