import ChosenNecklaceEnrichment
import ChosenNecklacePathMaps
import ChosenNecklaceOuterFlags

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T U V : NecklaceCode}

theorem vertexOrderMap_apply (f : NecklaceCode.Hom.{u} T U) (a : Vertices.{u} T) :
    vertexOrderMap f a = mapVertices f.map a := rfl

def NCMap (f : NecklaceCode.Hom.{u} T U) : NC.{u} T ⟶ NC.{u} U where
  obj a := ⟨vertexOrderMap f a.as⟩
  map a b := nerveMap (mapPathFunctor f a.as b.as)
  map_id a := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext Set.image_singleton)
  map_comp a b c := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext (Set.image_union _ _ _))

theorem NCMap_obj (f : NecklaceCode.Hom.{u} T U) (a : NecklaceThickening.{u} T) :
    (NCMap f).obj a = ⟨mapVertices f.map a.as⟩ := rfl

theorem NCMap_app (f : NecklaceCode.Hom.{u} T U) (a b : NecklaceThickening.{u} T)
    (n : ℕ) (P : (pathHom a b).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    (((NCMap f).map a b).app _ P).obj i = mapPath f (P.obj i) := rfl

theorem NCMap_operator (f : NecklaceCode.Hom.{u} T U)
    (a b : NecklaceThickening.{u} T) {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌)
    (P : (pathHom a b).obj (op ⦋n⦌)) :
    ((NCMap f).map a b).app _ ((pathHom a b).map α.op P) =
      (pathHom ((NCMap f).obj a) ((NCMap f).obj b)).map α.op
        (((NCMap f).map a b).app _ P) :=
  (congrFun (((NCMap f).map a b).naturality α.op) P).symm

def mapOuterPathFunctor (f : NecklaceCode.Hom.{u} T U) :
    OuterPath.{u} T ⥤ OuterPath.{u} U where
  obj P :=
    { toPath :=
        { I := mapVertices f.map '' P.I
          left := by
            refine ⟨ULift.up 0, P.left, ?_⟩
            apply ULift.ext
            exact orderMap_first f
          right := by
            refine ⟨ULift.up (Fin.last T.len), P.right, ?_⟩
            apply ULift.ext
            exact orderMap_last f
          left_le v _ := Fin.zero_le v.down
          le_right v _ := Fin.le_last v.down }
      joints j hj _ _ := by
        obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (joints_subset_image f hj)
        refine ⟨ULift.up v, P.joints v hv (Fin.zero_le v) (Fin.le_last v), ?_⟩
        exact ULift.ext _ _ he }
  map h := ⟨⟨⟨Set.image_mono h.1.1.1⟩⟩⟩

theorem outerFlagIso_naturality (f : NecklaceCode.Hom.{u} T U) :
    flagMap f ≫ (outerFlagIso U).hom =
      (outerFlagIso T).hom ≫ nerveMap (mapOuterPathFunctor f) := by
  ext q F
  exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
