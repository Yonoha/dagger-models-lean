import NativeSSetRawHomotopyEquivalenceWeak
import TopCatModelCategory.SSet.Contractible

/-!
# Native contraction of every standard simplex

Use Mathlib's standard-simplex/nerve isomorphism and the natural transformation
from the constant initial object of the finite ordinal to its identity functor.
The base point is exactly the original zeroth vertex of the standard simplex.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial Opposite
universe u
namespace DaggerNativeStandardSimplexContraction
noncomputable section

/-- The native zeroth vertex of the exact original standard simplex. -/
def firstVertex (n : ℕ) : (Δ[n] : SSet.{u}).obj (op ⦋0⦌) :=
  (SSet.stdSimplex.obj₀Equiv (n := n)).symm 0

/-- The constant initial object in the native finite ordinal used by `isoNerve`. -/
def initialFunctor (n : ℕ) : ULift.{u} (Fin (n + 1)) ⥤ ULift.{u} (Fin (n + 1)) :=
  (Functor.const (ULift.{u} (Fin (n + 1)))).obj ⟨0⟩

/-- Initiality gives the native natural transformation towards the identity. -/
def initialNatTrans (n : ℕ) : initialFunctor n ⟶ 𝟭 (ULift.{u} (Fin (n + 1))) where
  app k := homOfLE (show (⟨0⟩ : ULift.{u} (Fin (n + 1))) ≤ k from Fin.zero_le k.down)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Transport of the initial constant nerve map is the exact first-vertex constant map. -/
theorem initialNerveMap_transport (n : ℕ) :
    (SSet.stdSimplex.isoNerve.{u} n).hom ≫ nerveMap (initialFunctor n) ≫
      (SSet.stdSimplex.isoNerve.{u} n).inv = SSet.const (firstVertex n) := by
  apply NatTrans.ext
  funext d s
  ext i
  rfl

/-- The entire original standard simplex contracts to its native first vertex. -/
def simplexContractible (n : ℕ) : SSet.Contractible (Δ[n] : SSet.{u}) where
  pt := firstVertex n
  h := ((DaggerNerveHomotopy.natTransHomotopy (initialNatTrans n)).precomp
      (SSet.stdSimplex.isoNerve.{u} n).hom).postcomp
      (SSet.stdSimplex.isoNerve.{u} n).inv |>.congr
    (initialNerveMap_transport n) (by
      have hn : nerveMap (𝟭 (ULift.{u} (Fin (n + 1)))) =
          𝟙 (nerve (ULift.{u} (Fin (n + 1)))) := by
        apply NatTrans.ext
        funext d s
        exact Functor.comp_id s
      rw [hn, Category.comp_id, Iso.hom_inv_id])

end
end DaggerNativeStandardSimplexContraction
