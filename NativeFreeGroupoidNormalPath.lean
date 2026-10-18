import NativeFreeGroupoidReducedPaths

/-! Canonical native representatives and their length use the endpoint-preserving normal form. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeSignedPathWords DaggerNativeFreeGroupoidWordLabels
open DaggerNativeFreeGroupoidReducedPaths
universe u
namespace DaggerNativeFreeGroupoidNormalPath
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def normalPath {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) : Quiver.Path a b :=
  ((reducedPathEquiv V a b).symm f).val

theorem normalPath_reduced {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) :
    FreeGroup.IsReduced (word (normalPath V f)) :=
  ((reducedPathEquiv V a b).symm f).property

theorem quotient_normalPath {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) :
    (quotientMap V).map (normalPath V f) = f :=
  (reducedPathEquiv V a b).apply_symm_apply f

theorem normalPath_of_reduced {a b : Quiver.Symmetrify V} (p : Quiver.Path a b)
    (hp : FreeGroup.IsReduced (word p)) : normalPath V ((quotientMap V).map p) = p :=
  reduced_paths_equal_of_quotient_eq V _ p (normalPath_reduced V _) hp (quotient_normalPath V _)

def norm {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) : ℕ := (normalPath V f).length

theorem norm_of_reduced {a b : Quiver.Symmetrify V} (p : Quiver.Path a b)
    (hp : FreeGroup.IsReduced (word p)) : norm V ((quotientMap V).map p) = p.length := by
  rw [norm, normalPath_of_reduced V p hp]

theorem norm_id (a : Quiver.Symmetrify V) : norm V (𝟙 ((quotientMap V).obj a)) = 0 :=
  norm_of_reduced V (.nil : Quiver.Path a a) FreeGroup.IsReduced.nil

end
end DaggerNativeFreeGroupoidNormalPath
