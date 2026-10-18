import NativePrefixMappingTransportIso
import TopCatModelCategory.ModelCategorySSet

/-! Exact weak transport of full prefix-mapping maps through an actual ambient iso square. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalOrdinalJoinLeft DaggerActualQuasicategoryMappingFibres
open DaggerNativePrefixMappingTransportIso
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePrefixMappingWeakIsoSquare
noncomputable section

variable {A B A' B' : SSet.{u}} (f : A ⟶ B) (g : A' ⟶ B')
variable (eA : A ≅ A') (eB : B ≅ B') (h : eA.hom ≫ g = f ≫ eB.hom)
variable (k : SimplexCategory) (σ : A.obj (op k)) (b : A.obj (op ⦋0⦌))

def squareMap :
    prefixMapping A' k (eA.hom.app (op k) σ) (eA.hom.app (op ⦋0⦌) b) ⟶
      prefixMapping B' k (eB.hom.app (op k) (f.app (op k) σ))
        (eB.hom.app (op ⦋0⦌) (f.app (op ⦋0⦌) b)) :=
  mapTo g k (eA.hom.app (op k) σ) (eA.hom.app (op ⦋0⦌) b)
    (eB.hom.app (op k) (f.app (op k) σ))
    (eB.hom.app (op ⦋0⦌) (f.app (op ⦋0⦌) b))
    (congrFun (NatTrans.congr_app h (op k)) σ)
    (congrFun (NatTrans.congr_app h (op ⦋0⦌)) b)

def sourceIso := mappingIso eA k σ b _ _ rfl rfl

def targetIso := mappingIso eB k (f.app (op k) σ) (f.app (op ⦋0⦌) b) _ _ rfl rfl

theorem square : (sourceIso eA k σ b).hom ≫ squareMap f g eA eB h k σ b =
    map f k σ b ≫ (targetIso f eB k σ b).hom := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  apply Subtype.ext
  change ((mapTo g k _ _ _ _ _ _).app q
      ((mapTo eA.hom k _ _ _ _ rfl rfl).app q s)).val.val =
    ((mapTo eB.hom k _ _ _ _ rfl rfl).app q ((map f k σ b).app q s)).val.val
  rw [mapTo_raw, mapTo_raw, mapTo_raw]
  exact congrFun (NatTrans.congr_app h (op ((ordinalJoinLeft k).obj q.unop))) s.val.val

theorem map_weak_iff : WeakEquivalence (map f k σ b) ↔
    WeakEquivalence (squareMap f g eA eB h k σ b) := by
  let E := (sourceIso eA k σ b).hom
  let F := (targetIso f eB k σ b).hom
  let G := squareMap f g eA eB h k σ b
  have hs : E ≫ G = map f k σ b ≫ F := square f g eA eB h k σ b
  constructor
  · intro hw
    have := hw
    have hc : WeakEquivalence (map f k σ b ≫ F) := inferInstance
    have : WeakEquivalence (E ≫ G) := hs.symm ▸ hc
    exact weakEquivalence_of_precomp E G
  · intro hw
    have := hw
    have hc : WeakEquivalence (E ≫ G) := inferInstance
    have : WeakEquivalence (map f k σ b ≫ F) := hs ▸ hc
    exact weakEquivalence_of_postcomp (map f k σ b) F

end
end DaggerNativePrefixMappingWeakIsoSquare
