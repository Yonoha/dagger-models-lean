import ChosenNecklaceSliceCoconeMaps
import ChosenEnrichedFunctorMapEquality

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
variable {D : DaggerModels.SimplicialCat.{u,u}}
variable (F : slice.{u} T j false ⟶ D) (G : slice.{u} T j true ⟶ D)
variable (h : F.obj (sliceJoint T j false) = G.obj (sliceJoint T j true))

/-- Complete arbitrary-target enriched descent at an actual original joint. -/
def sliceDesc : NC.{u} T ⟶ D := (sliceCoconeMaps j F G h).desc hj

theorem sliceDesc_left : sliceInclusion T j false ≫ sliceDesc j hj F G h = F := by
  calc
    _ = leftAligned j F G := by
      have ho : ∀ a : (slice.{u} T j false).Obj,
          (sliceInclusion T j false ≫ sliceDesc j hj F G h).obj a =
            (leftAligned j F G).obj a := fun _ ↦ rfl
      apply EnrichedFunctor.ext SSet ho
      intro a b
      apply NatTrans.ext
      funext q z
      exact glueChain_left q j hj (sliceCoconeMaps j F G h) a.property b.property z
    _ = F := transportObjects_eq _ _ _

theorem sliceDesc_right : sliceInclusion T j true ≫ sliceDesc j hj F G h = G := by
  calc
    _ = rightAligned j F G h := by
      have ho : ∀ a : (slice.{u} T j true).Obj,
          (sliceInclusion T j true ≫ sliceDesc j hj F G h).obj a =
            (rightAligned j F G h).obj a := fun _ ↦ rfl
      apply EnrichedFunctor.ext SSet ho
      intro a b
      apply NatTrans.ext
      funext q z
      exact glueChain_right q j hj (sliceCoconeMaps j F G h) a.property b.property z
    _ = G := transportObjects_eq _ _ _

/-- Whole uniqueness, including every crossing Hom, from the actual original split composition. -/
theorem sliceDesc_uniq (K : NC.{u} T ⟶ D)
    (hKF : sliceInclusion T j false ≫ K = F)
    (hKG : sliceInclusion T j true ≫ K = G) : K = sliceDesc j hj F G h := by
  have hkobj : ∀ a : (NC.{u} T).Obj, K.obj a = sliceLabel j F G a.as := by
    intro a
    by_cases ha : a.as ≤ ULift.up j
    · rw [sliceLabel, dif_pos ha]
      exact congrArg (fun L ↦ L.obj ⟨a.as, ha⟩) hKF
    · rw [sliceLabel, dif_neg ha]
      exact congrArg (fun L ↦ L.obj ⟨a.as, (lt_of_not_ge ha).le⟩) hKG
  let L := transportObjects K (fun a ↦ sliceLabel j F G a.as) hkobj
  have hLF : sliceInclusion T j false ≫ L = leftAligned j F G := by
    simpa only [L, leftAligned, transportObjects_eq] using hKF
  have hLG : sliceInclusion T j true ≫ L = rightAligned j F G h := by
    simpa only [L, rightAligned, transportObjects_eq] using hKG
  have hl : ∀ a b : (slice.{u} T j false).Obj,
      L.map ⟨a.val⟩ ⟨b.val⟩ = (leftAligned j F G).map a b := by
    intro a b
    have hm := enrichedFunctor_hom_congr hLF a b rfl rfl
    simpa only [DaggerModels.SimplicialCat.comp_map, sliceInclusion_hom,
      targetHomTransport, eqToHom_refl, Category.id_comp, Category.comp_id] using hm
  have hr : ∀ a b : (slice.{u} T j true).Obj,
      L.map ⟨a.val⟩ ⟨b.val⟩ = (rightAligned j F G h).map a b := by
    intro a b
    have hm := enrichedFunctor_hom_congr hLG a b rfl rfl
    simpa only [DaggerModels.SimplicialCat.comp_map, sliceInclusion_hom,
      targetHomTransport, eqToHom_refl, Category.id_comp, Category.comp_id] using hm
  have hL : L = sliceDesc j hj F G h := by
    have ho : ∀ a : (NC.{u} T).Obj, L.obj a = (sliceDesc j hj F G h).obj a := fun _ ↦ rfl
    apply EnrichedFunctor.ext SSet ho
    intro a b
    apply NatTrans.ext
    funext q z
    change (L.map a b).app q z =
      glueChain q j hj ((sliceCoconeMaps j F G h).degree q) z
    by_cases ha : ULift.up j ≤ a.as
    · simp only [glueChain, dif_pos ha]
      exact congrFun (NatTrans.congr_app
        (hr ⟨a.as, ha⟩ ⟨b.as, ha.trans (chain_le q z)⟩) q) z
    · by_cases hb : ULift.up j ≤ b.as
      · simp only [glueChain, dif_neg ha, dif_pos hb]
        let ha' := le_of_lt (lt_of_not_ge ha)
        have hh := congrFun (NatTrans.congr_app (L.map_comp a ⟨ULift.up j⟩ b) q)
          (splitChainLeft q j hj ha' hb z, splitChainRight q j hj ha' hb z)
        change (L.map a b).app q
          (chainComp q (splitChainLeft q j hj ha' hb z)
            (splitChainRight q j hj ha' hb z)) = _ at hh
        rw [chain_split_comp q j hj ha' hb z] at hh
        have hl' : L.map a ⟨ULift.up j⟩ =
            (leftAligned j F G).map ⟨a.as, ha'⟩ ⟨ULift.up j, le_rfl⟩ :=
          hl ⟨a.as, ha'⟩ ⟨ULift.up j, le_rfl⟩
        have hr' : L.map ⟨ULift.up j⟩ b =
            (rightAligned j F G h).map ⟨ULift.up j, le_rfl⟩ ⟨b.as, hb⟩ :=
          hr ⟨ULift.up j, le_rfl⟩ ⟨b.as, hb⟩
        rw [hl', hr'] at hh
        exact hh
      · simp only [glueChain, dif_neg ha, dif_neg hb]
        exact congrFun (NatTrans.congr_app
          (hl ⟨a.as, (lt_of_not_ge ha).le⟩ ⟨b.as, (lt_of_not_ge hb).le⟩) q) z
  exact (transportObjects_eq K _ hkobj).symm.trans hL

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
