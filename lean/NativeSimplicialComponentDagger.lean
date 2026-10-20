import ActualPiZeroConstantAdjunction
import DaggerModels

/-! The original dagger acts on component categories and preserves all isomorphisms. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroCategory
universe u
namespace DaggerNativeSimplicialComponentDagger
noncomputable section

def componentDagger (D : DaggerSimplicialCat.{u, u}) :
    DaggerCategory (componentObjects D.toSimplicialCat) where
  dagger {x y} f := SSet.mapπ₀ (D.daggerStructure.dagger x y) f
  dagger_involutive {x y} f := by
    obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective f
    change SSet.π₀.mk ((D.daggerStructure.dagger y x).app (op ⦋0⦌)
      ((D.daggerStructure.dagger x y).app (op ⦋0⦌) v)) = SSet.π₀.mk v
    exact congrArg SSet.π₀.mk
      (congrFun (NatTrans.congr_app (D.daggerStructure.dagger_involutive x y) (op ⦋0⦌)) v)
  dagger_id x := by
    change SSet.π₀.mk ((D.daggerStructure.dagger x x).app (op ⦋0⦌)
      ((D.enriched.id x).app (op ⦋0⦌) PUnit.unit)) =
      SSet.π₀.mk ((D.enriched.id x).app (op ⦋0⦌) PUnit.unit)
    exact congrArg SSet.π₀.mk
      (congrFun (NatTrans.congr_app (D.daggerStructure.dagger_id x) (op ⦋0⦌)) PUnit.unit)
  dagger_comp {x y z} f g := by
    obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective f
    obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective g
    change SSet.π₀.mk ((D.daggerStructure.dagger x z).app (op ⦋0⦌)
      ((D.enriched.comp x y z).app (op ⦋0⦌) (v, w))) =
      SSet.π₀.mk ((D.enriched.comp z y x).app (op ⦋0⦌)
        ((D.daggerStructure.dagger y z).app (op ⦋0⦌) w,
          (D.daggerStructure.dagger x y).app (op ⦋0⦌) v))
    exact congrArg SSet.π₀.mk
      (congrFun (NatTrans.congr_app (D.daggerStructure.dagger_comp x y z) (op ⦋0⦌)) (v, w))

theorem dagger_isIso {A : Type u} [Category.{u} A] [DaggerCategory A]
    {x y : A} (f : x ⟶ y) [IsIso f] : IsIso (DaggerCategory.dagger f) := by
  refine ⟨⟨DaggerCategory.dagger (inv f), ?_, ?_⟩⟩
  · rw [← DaggerCategory.dagger_comp, IsIso.inv_hom_id, DaggerCategory.dagger_id]
  · rw [← DaggerCategory.dagger_comp, IsIso.hom_inv_id, DaggerCategory.dagger_id]

end
end DaggerNativeSimplicialComponentDagger
