import OriginalNecklaceCutMaps

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {S T : NecklaceCode} (g : NecklaceCode.Hom.{u} S T)
  (k : Fin (S.len + 1)) (l : Fin (T.len + 1)) (h : orderMap g.map k = l)

/-- The original cut-wedge arrows commute with every map preserving the specified cuts. -/
theorem cutWedgeHom_naturality :
    NecklaceCode.Hom.comp (cutWedgeHom S k) g =
      NecklaceCode.Hom.comp (wedgeMap (cutLeftHom g k l h) (cutRightHom g k l h))
        (cutWedgeHom T l) := by
  apply NecklaceCode.Hom.ext
  change cutWedgeMap S k ≫ g.map =
    (wedgeMap (cutLeftHom g k l h) (cutRightHom g k l h)).map ≫ cutWedgeMap T l
  apply (wedgeIsPushout (cutLeft S k) (cutRight S k)).hom_ext
  · rw [← Category.assoc, cutWedge_left, ← Category.assoc, wedgeMap_left,
      Category.assoc, cutWedge_left]
    exact (cutLeftHom_fac g k l h).symm
  · rw [← Category.assoc, cutWedge_right, ← Category.assoc, wedgeMap_right,
      Category.assoc, cutWedge_right]
    exact (cutRightHom_fac g k l h).symm

variable (hk : k ∈ S.joints) (hl : l ∈ T.joints)

/-- Naturality of the inverse with the literal flag maps and no injectivity assumption on g. -/
theorem cutFlagInv_map {n : ℕ}
    (F : Flag.{u} (cutLeft S k) n) (G : Flag.{u} (cutRight S k) n) :
    NecklaceCode.Flag.map g ((cutFlagIso S k hk).inv.app (op ⦋n⦌) (F, G)) =
      (cutFlagIso T l hl).inv.app (op ⦋n⦌)
        (NecklaceCode.Flag.map (cutLeftHom g k l h) F,
          NecklaceCode.Flag.map (cutRightHom g k l h) G) := by
  calc
    _ = NecklaceCode.Flag.map g
        (NecklaceCode.Flag.map (cutWedgeHom S k) (NecklaceCode.Flag.wedge F G)) :=
      congrArg (NecklaceCode.Flag.map g) (cutWedge_flag S k hk F G).symm
    _ = NecklaceCode.Flag.map (NecklaceCode.Hom.comp (cutWedgeHom S k) g)
        (NecklaceCode.Flag.wedge F G) := (NecklaceCode.Flag.map_comp _ _ _).symm
    _ = NecklaceCode.Flag.map
        (NecklaceCode.Hom.comp (wedgeMap (cutLeftHom g k l h) (cutRightHom g k l h))
          (cutWedgeHom T l)) (NecklaceCode.Flag.wedge F G) := by
      rw [cutWedgeHom_naturality g k l h]
    _ = NecklaceCode.Flag.map (cutWedgeHom T l)
        (NecklaceCode.Flag.wedge (NecklaceCode.Flag.map (cutLeftHom g k l h) F)
          (NecklaceCode.Flag.map (cutRightHom g k l h) G)) := by
      rw [NecklaceCode.Flag.map_comp, NecklaceCode.Flag.wedge_map]
    _ = _ := cutWedge_flag T l hl _ _

theorem cutFlagIso_inv_naturality :
    (cutFlagIso S k hk).inv ≫ flagMap g =
      (flagMap (cutLeftHom g k l h) ⊗ₘ flagMap (cutRightHom g k l h)) ≫
        (cutFlagIso T l hl).inv := by
  apply NatTrans.ext
  funext q F
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  exact cutFlagInv_map g k l h hk hl F.1 F.2

/-- The whole simplicial-set splitting commutes with every cut-preserving necklace map. -/
theorem cutFlagIso_naturality :
    flagMap g ≫ (cutFlagIso T l hl).hom =
      (cutFlagIso S k hk).hom ≫
        (flagMap (cutLeftHom g k l h) ⊗ₘ flagMap (cutRightHom g k l h)) := by
  apply (cancel_mono (cutFlagIso T l hl).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc,
    ← cutFlagIso_inv_naturality g k l h hk hl, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

end

end DaggerOriginalProductGadget
