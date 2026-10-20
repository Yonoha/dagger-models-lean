import OrdinaryCellComparisonStages

/-! The same comparative map at any two original mono-cell pushout apexes. -/
open CategoryTheory MonoidalCategory Limits DaggerModels
open DaggerRelativeOneCellPresentation DaggerOrdinaryCellImage

universe u
set_option autoImplicit false
namespace DaggerOrdinaryCellComparisonData
noncomputable section

variable {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) {K L : SSet.{u}}
  (k : K ⟶ L) [Mono k] (u0 : K ⟶ (x ⟶[SSet] y))

theorem image_attaching_map :
    attachingMap k (u0 ≫ F.map x y) = attachingMap k u0 ≫ F.map x y :=
  (Category.assoc _ _ _).symm

/-- The actual canonical range comparison; its compatibility has no caller premise. -/
def imageQF : Q C x y (DaggerOrdinaryCellImage.image k).ι (attachingMap k u0) ⟶
    Q D (F.obj x) (F.obj y) (DaggerOrdinaryCellImage.image k).ι (attachingMap k (u0 ≫ F.map x y)) :=
  QF F x y (DaggerOrdinaryCellImage.image k) (attachingMap k u0) (attachingMap k (u0 ≫ F.map x y))
    (image_attaching_map F x y k u0).symm

variable {PC PD : SimplicialCat.{u, u}}
  (gC : OrdinaryTwoObjectCell.cell L ⟶ PC) (iC : C ⟶ PC)
  (sqC : IsPushout (OrdinaryTwoObjectCell.map k)
    (OrdinaryTwoObjectCell.fromData K C x y u0) gC iC)
  (gD : OrdinaryTwoObjectCell.cell L ⟶ PD) (iD : D ⟶ PD)
  (sqD : IsPushout (OrdinaryTwoObjectCell.map k)
    (OrdinaryTwoObjectCell.fromData K D (F.obj x) (F.obj y) (u0 ≫ F.map x y)) gD iD)

def sourceIso : Q C x y (DaggerOrdinaryCellImage.image k).ι (attachingMap k u0) ≅ PC :=
  originalIso C x y (DaggerOrdinaryCellImage.image k).ι (attachingMap k u0) gC iC
    (pushoutToImage k C PC x y u0 gC iC sqC)

def targetIso :
    Q D (F.obj x) (F.obj y) (DaggerOrdinaryCellImage.image k).ι
      (attachingMap k (u0 ≫ F.map x y)) ≅ PD :=
  originalIso D (F.obj x) (F.obj y) (DaggerOrdinaryCellImage.image k).ι
    (attachingMap k (u0 ≫ F.map x y)) gD iD
    (pushoutToImage k D PD (F.obj x) (F.obj y) (u0 ≫ F.map x y) gD iD sqD)

theorem sourceIso_old :
    v C x y (DaggerOrdinaryCellImage.image k).ι (attachingMap k u0) ≫
      (sourceIso x y k u0 gC iC sqC).hom = iC := v_originalIso ..

theorem sourceIso_new :
    t C x y (DaggerOrdinaryCellImage.image k).ι (attachingMap k u0) ≫
      (sourceIso x y k u0 gC iC sqC).hom = gC := t_originalIso ..

theorem targetIso_old :
    v D (F.obj x) (F.obj y) (DaggerOrdinaryCellImage.image k).ι (attachingMap k (u0 ≫ F.map x y)) ≫
      (targetIso F x y k u0 gD iD sqD).hom = iD := v_originalIso ..

theorem targetIso_new :
    t D (F.obj x) (F.obj y) (DaggerOrdinaryCellImage.image k).ι (attachingMap k (u0 ≫ F.map x y)) ≫
      (targetIso F x y k u0 gD iD sqD).hom = gD := t_originalIso ..

variable (Fplus : PC ⟶ PD) (hOld : iC ≫ Fplus = F ≫ iD) (hNew : gC ≫ Fplus = gD)

/- Full functor equality with the supplied arbitrary-apex comparison, not only its objects. -/
include hOld hNew in
theorem original_comparison :
    (sourceIso x y k u0 gC iC sqC).hom ≫ Fplus ≫
        (targetIso F x y k u0 gD iD sqD).inv = imageQF F x y k u0 := by
  apply hom_ext C x y (DaggerOrdinaryCellImage.image k).ι (attachingMap k u0)
  · rw [← Category.assoc, ← Category.assoc, sourceIso_old, hOld]
    rw [Category.assoc]
    dsimp only [targetIso]
    rw [f_originalIso_inv]
    exact (QF_old ..).symm
  · rw [← Category.assoc, ← Category.assoc, sourceIso_new, hNew]
    dsimp only [targetIso]
    rw [g_originalIso_inv]
    exact (QF_cell ..).symm

include hOld hNew in
theorem original_comparison_hom :
    (sourceIso x y k u0 gC iC sqC).hom ≫ Fplus =
      imageQF F x y k u0 ≫ (targetIso F x y k u0 gD iD sqD).hom := by
  rw [← original_comparison F x y k u0 gC iC sqC gD iD sqD Fplus hOld hNew]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

include hOld hNew in
theorem original_comparison_inv :
    Fplus = (sourceIso x y k u0 gC iC sqC).inv ≫ imageQF F x y k u0 ≫
      (targetIso F x y k u0 gD iD sqD).hom := by
  rw [← original_comparison_hom F x y k u0 gC iC sqC gD iD sqD Fplus hOld hNew]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/- Every original new apex object is still represented by an original old object. -/
include gC sqC in
theorem source_object_coverage (p : PC.Obj) : ∃ a : C.Obj, iC.obj a = p := by
  let a := (sourceIso x y k u0 gC iC sqC).inv.obj p
  refine ⟨a, ?_⟩
  have h := congrArg (fun H : PC ⟶ PC ↦ H.obj p)
    (sourceIso x y k u0 gC iC sqC).inv_hom_id
  change (sourceIso x y k u0 gC iC sqC).hom.obj a = p at h
  dsimp only [sourceIso] at h
  rw [originalIso_obj] at h
  exact h

/-- Full original Hom equation, including target endpoint transports from the whole equality. -/
theorem original_comparison_map (a b : C.Obj) :
    ((sourceIso x y k u0 gC iC sqC).hom ≫ Fplus).map a b ≫
        eqToHom (by
          rw [show ((sourceIso x y k u0 gC iC sqC).hom ≫ Fplus).obj a =
            (imageQF F x y k u0 ≫ (targetIso F x y k u0 gD iD sqD).hom).obj a from
              congrArg (fun H ↦ H.obj a)
                (original_comparison_hom F x y k u0 gC iC sqC gD iD sqD Fplus hOld hNew),
            show ((sourceIso x y k u0 gC iC sqC).hom ≫ Fplus).obj b =
            (imageQF F x y k u0 ≫ (targetIso F x y k u0 gD iD sqD).hom).obj b from
              congrArg (fun H ↦ H.obj b)
                (original_comparison_hom F x y k u0 gC iC sqC gD iD sqD Fplus hOld hNew)]) =
      (imageQF F x y k u0 ≫ (targetIso F x y k u0 gD iD sqD).hom).map a b :=
  enriched_congr_map
    (original_comparison_hom F x y k u0 gC iC sqC gD iD sqD Fplus hOld hNew) a b

end
end DaggerOrdinaryCellComparisonData
