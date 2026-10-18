import NativeFamilyWeak

/-! The unchanged pointwise family preserves exact isomorphisms component by component. -/
set_option autoImplicit false
open CategoryTheory
open DaggerOriginalProductGadget DaggerNativeFamilyWeak
universe u
namespace DaggerNativeFamilyIsomorphisms
noncomputable section

def familyIso {I : Type u} {X Y : I → SSet.{u}} (e : ∀ i, X i ≅ Y i) :
    familySSet X ≅ familySSet Y where
  hom := familyMap (fun i ↦ (e i).hom)
  inv := familyMap (fun i ↦ (e i).inv)
  hom_inv_id := by
    apply NatTrans.ext
    funext n b
    rcases b with ⟨i, a⟩
    exact congrArg (fun t : (X i).obj n ↦ (⟨i, t⟩ : Σ i, (X i).obj n))
      (congrFun (NatTrans.congr_app (e i).hom_inv_id n) a)
  inv_hom_id := by
    apply NatTrans.ext
    funext n b
    rcases b with ⟨i, a⟩
    exact congrArg (fun t : (Y i).obj n ↦ (⟨i, t⟩ : Σ i, (Y i).obj n))
      (congrFun (NatTrans.congr_app (e i).inv_hom_id n) a)

end
end DaggerNativeFamilyIsomorphisms
