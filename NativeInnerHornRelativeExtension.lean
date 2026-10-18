import NativeInnerHornFacePostcomposition
import OriginalInnerHornNerveFiller

/-! Relative lifting of the ORIGINAL inner-horn enriched extension, without Kan input premises. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
open DaggerOrdinaryRigidificationCof
open DaggerOrdinaryRigidificationCof.BoundaryData
open DaggerOrdinaryRigidificationCof.PathFacets
open DaggerOrdinaryRigidificationCof.InnerHornFaces
open DaggerOrdinaryRigidificationCof.InnerHornCompleteMaps
open DaggerNativeInnerHornFacePostcomposition
universe u
namespace DaggerNativeInnerHornRelativeExtension
noncomputable section
variable {n : ℕ} {C B : SC.{u}} (k : interior n)
variable (D : CompatibleFaceData (n + 1) C (Admissible k)) (p : C ⟶ B)

theorem completeMap_post
    (ell : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
    (i j : Fin (n + 2)) :
    InnerHornCompleteMaps.completeMap k (post D p)
        (ell ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1)))) i j =
      InnerHornCompleteMaps.completeMap k D ell i j ≫ p.map (D.obj i) (D.obj j) := by
  by_cases h : i = 0 ∧ j = Fin.last (n + 1)
  · rcases h with ⟨rfl, rfl⟩
    rw [InnerHornCompleteMaps.completeMap_extreme, InnerHornCompleteMaps.completeMap_extreme]
  · rw [InnerHornCompleteMaps.completeMap_proper k (post D p) _ i j h,
      InnerHornCompleteMaps.completeMap_proper k D ell i j h]
    exact properMap_post k D p i j h

theorem mapped_boundary
    (ell : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
    (h : (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D) :
    (extremeHorn n k).ι ≫ (ell ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1)))) =
      InnerHornGlue.hornMap k (post D p) := by
  rw [← Category.assoc, h, hornMap_post]

theorem extensionFunctor_post
    (ell : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
    (h : (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D) :
    InnerHornExtension.extensionFunctor k (post D p)
        (ell ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1)))) (mapped_boundary k D p ell h) =
      InnerHornExtension.extensionFunctor k D ell h ≫ p := by
  apply EnrichedFunctor.ext SSet
    (F := InnerHornExtension.extensionFunctor k (post D p)
      (ell ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1)))) (mapped_boundary k D p ell h))
    (G := EnrichedFunctor.comp SSet (InnerHornExtension.extensionFunctor k D ell h) p)
    (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact completeMap_post k D p ell x.as.down y.as.down

theorem extensionFunctor_congr
    (ell ell' : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
    (e : ell = ell') (h : (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D)
    (h' : (extremeHorn n k).ι ≫ ell' = InnerHornGlue.hornMap k D) :
    InnerHornExtension.extensionFunctor k D ell h =
      InnerHornExtension.extensionFunctor k D ell' h' := by
  cases e
  rfl

theorem relative_extreme_extension
    (hp : Fibration (p.map (D.obj 0) (D.obj (Fin.last (n + 1)))))
    (ellB : extremeHom.{u} n ⟶ ((post D p).obj 0 ⟶[SSet.{u}]
      (post D p).obj (Fin.last (n + 1))))
    (hB : (extremeHorn n k).ι ≫ ellB = InnerHornGlue.hornMap k (post D p)) :
    ∃ ell : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))),
      (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D ∧
        ell ≫ p.map (D.obj 0) (D.obj (Fin.last (n + 1))) = ellB := by
  have := extremeHorn_lifting n k (p.map (D.obj 0) (D.obj (Fin.last (n + 1)))) hp
  let sq : CommSq (InnerHornGlue.hornMap k D) (extremeHorn n k).ι
      (p.map (D.obj 0) (D.obj (Fin.last (n + 1)))) ellB :=
    ⟨(hB.trans (hornMap_post k D p)).symm⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

theorem relative_functor_extension
    (hp : Fibration (p.map (D.obj 0) (D.obj (Fin.last (n + 1)))))
    (ellB : extremeHom.{u} n ⟶ ((post D p).obj 0 ⟶[SSet.{u}]
      (post D p).obj (Fin.last (n + 1))))
    (hB : (extremeHorn n k).ι ≫ ellB = InnerHornGlue.hornMap k (post D p)) :
    ∃ (ell : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
      (h : (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D),
      InnerHornExtension.extensionFunctor k D ell h ≫ p =
        InnerHornExtension.extensionFunctor k (post D p) ellB hB := by
  obtain ⟨ell, h, he⟩ := relative_extreme_extension k D p hp ellB hB
  refine ⟨ell, h, ?_⟩
  exact (extensionFunctor_post k D p ell h).symm.trans
    (extensionFunctor_congr k (post D p) _ _ he _ hB)

end
end DaggerNativeInnerHornRelativeExtension
