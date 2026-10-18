import NativeFiniteLineNerve
import NativeFreePathSpineInner
import NativeSubcomplexImageIso

/-! The native standard spine retains all original values and has an inner-anodyne inclusion. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeFiniteLinePaths DaggerNativeFiniteLineNerve
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathSpineInner
open DaggerNativeInnerHornFactorization DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeStandardSpineInner
noncomputable section

def spine (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  (generatorSpine (Vertex.{u} n)).image (simplexIso.{u} n).hom

theorem inclusion_innerAnodyne (n : ℕ) : innerAnodyne (spine.{u} n).ι :=
  DaggerNativeSubcomplexImageIso.image_innerAnodyne (simplexIso n)
    (generatorSpine (Vertex n)) (generatorSpine_innerAnodyne (Vertex n))

theorem inclusion_categorical_weak (n : ℕ) : weakCategoricalEquivalences (spine.{u} n).ι :=
  DaggerNativeInnerJoyalMappingWeak.innerAnodyne_weak _ (inclusion_innerAnodyne n)

theorem mem_spine_iff {n d : ℕ} (c : (Δ[n] : SSet.{u}).obj (op ⦋d⦌)) :
    c ∈ (spine n).obj (op ⦋d⦌) ↔
      (SSet.stdSimplex.asOrderHom c (Fin.last d)).val ≤
        (SSet.stdSimplex.asOrderHom c 0).val + 1 := by
  constructor
  · rintro ⟨t, ht, he⟩
    have hd := path_distance (totalPath t)
    change (t.obj 0).index.val + (totalPath t).length =
      (t.obj (Fin.last d)).index.val at hd
    have hw : (totalPath t).length ≤ 1 := ht
    have h0 := simplexIso_hom_value (n := n) (d := d) t (0 : Fin (d + 1))
    have h1 := simplexIso_hom_value (n := n) (d := d) t (Fin.last d)
    rw [he] at h0 h1
    rw [h0, h1]
    omega
  · intro hc
    let t := (simplexIso n).inv.app (op ⦋d⦌) c
    have hd := path_distance (totalPath t)
    have h0 := simplexIso_inv_value c (0 : Fin (d + 1))
    have h1 := simplexIso_inv_value c (Fin.last d)
    have hw : (totalPath t).length ≤ 1 := by
      change (t.obj 0).index.val + (totalPath t).length =
        (t.obj (Fin.last d)).index.val at hd
      change (t.obj 0).index = _ at h0
      change (t.obj (Fin.last d)).index = _ at h1
      rw [h0, h1] at hd
      omega
    refine ⟨t, hw, ?_⟩
    exact congrFun (NatTrans.congr_app (simplexIso n).inv_hom_id (op ⦋d⦌)) c

end
end DaggerNativeStandardSpineInner
