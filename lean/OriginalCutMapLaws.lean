import OriginalNecklaceCutMaps

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

theorem orderMap_id_apply (S : NecklaceCode) (k : Fin (S.len + 1)) :
    orderMap (NecklaceCode.Hom.id.{u} S).map k = k := by
  change (mapVertices (𝟙 (toSSet.{u} S)) (ULift.up k)).down = k
  rw [mapVertices_id]
  rfl

theorem cutLeftHom_id (S : NecklaceCode) (k : Fin (S.len + 1)) :
    cutLeftHom (NecklaceCode.Hom.id S) k k (orderMap_id_apply S k) =
      NecklaceCode.Hom.id.{u} (cutLeft S k) := by
  apply NecklaceCode.Hom.ext
  have : Mono (cutLeftι S k) :=
    inferInstanceAs (Mono (intervalι S 0 k (Fin.zero_le k)))
  apply (cancel_mono (cutLeftι S k)).mp
  rw [cutLeftHom_fac]
  change cutLeftι S k ≫ 𝟙 _ = 𝟙 _ ≫ cutLeftι S k
  simp

theorem cutRightHom_id (S : NecklaceCode) (k : Fin (S.len + 1)) :
    cutRightHom (NecklaceCode.Hom.id S) k k (orderMap_id_apply S k) =
      NecklaceCode.Hom.id.{u} (cutRight S k) := by
  apply NecklaceCode.Hom.ext
  have : Mono (cutRightι S k) :=
    inferInstanceAs (Mono (intervalι S k (Fin.last S.len) (Fin.le_last k)))
  apply (cancel_mono (cutRightι S k)).mp
  rw [cutRightHom_fac]
  change cutRightι S k ≫ 𝟙 _ = 𝟙 _ ≫ cutRightι S k
  simp

variable {S T U : NecklaceCode} (f : NecklaceCode.Hom.{u} S T)
  (g : NecklaceCode.Hom.{u} T U)
  (k : Fin (S.len + 1)) (l : Fin (T.len + 1)) (m : Fin (U.len + 1))
  (hf : orderMap f.map k = l) (hg : orderMap g.map l = m)

include hf hg in
theorem cutJoint_comp : orderMap (NecklaceCode.Hom.comp f g).map k = m := by
  change orderMap (f.map ≫ g.map) k = m
  rw [orderMap_comp_apply, hf, hg]

theorem cutLeftHom_comp :
    cutLeftHom (NecklaceCode.Hom.comp f g) k m (cutJoint_comp f g k l m hf hg) =
      NecklaceCode.Hom.comp (cutLeftHom f k l hf) (cutLeftHom g l m hg) := by
  apply NecklaceCode.Hom.ext
  have : Mono (cutLeftι U m) :=
    inferInstanceAs (Mono (intervalι U 0 m (Fin.zero_le m)))
  apply (cancel_mono (cutLeftι U m)).mp
  rw [cutLeftHom_fac]
  change cutLeftι S k ≫ (f.map ≫ g.map) =
    ((cutLeftHom f k l hf).map ≫ (cutLeftHom g l m hg).map) ≫ cutLeftι U m
  rw [Category.assoc, cutLeftHom_fac,
    ← Category.assoc (cutLeftHom f k l hf).map (cutLeftι T l) g.map,
    cutLeftHom_fac, Category.assoc]

theorem cutRightHom_comp :
    cutRightHom (NecklaceCode.Hom.comp f g) k m (cutJoint_comp f g k l m hf hg) =
      NecklaceCode.Hom.comp (cutRightHom f k l hf) (cutRightHom g l m hg) := by
  apply NecklaceCode.Hom.ext
  have : Mono (cutRightι U m) :=
    inferInstanceAs (Mono (intervalι U m (Fin.last U.len) (Fin.le_last m)))
  apply (cancel_mono (cutRightι U m)).mp
  rw [cutRightHom_fac]
  change cutRightι S k ≫ (f.map ≫ g.map) =
    ((cutRightHom f k l hf).map ≫ (cutRightHom g l m hg).map) ≫ cutRightι U m
  rw [Category.assoc, cutRightHom_fac,
    ← Category.assoc (cutRightHom f k l hf).map (cutRightι T l) g.map,
    cutRightHom_fac, Category.assoc]

end

end DaggerOriginalProductGadget
