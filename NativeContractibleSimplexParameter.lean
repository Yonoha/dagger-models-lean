import NativeStandardSimplexContraction

/-!
# Removing a contractible simplicial parameter preserves native weak equivalence

The section inserts the supplied original point and keeps the other coordinate.
Its two composites are controlled by the given raw contraction and the native
cartesian projection. No Kan or cofibrancy hypothesis is imposed on the other
original simplicial set.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra Simplicial
open DaggerNativeSSetRawHomotopyEquivalenceWeak
open DaggerNativeStandardSimplexContraction
universe u
namespace DaggerNativeContractibleSimplexParameter
noncomputable section

/-- Insert exactly the supplied point, retaining every simplex in the second coordinate. -/
def pointSection {K : SSet.{u}} (c : K.Contractible) (Y : SSet.{u}) : Y ⟶ K ⊗ Y :=
  lift (SSet.const c.pt) (𝟙 Y)

/-- The supplied-point section is an actual section of the native projection. -/
theorem pointSection_snd {K : SSet.{u}} (c : K.Contractible) (Y : SSet.{u}) :
    pointSection c Y ≫ snd K Y = 𝟙 Y := by
  apply NatTrans.ext
  funext n y
  rfl

/-- The exact native projection has the supplied-point section as a raw homotopy inverse. -/
def projectionHomotopyEquiv {K : SSet.{u}} (c : K.Contractible) (Y : SSet.{u}) :
    SSet.HomotopyEquiv (K ⊗ Y) Y where
  hom := snd K Y
  inv := pointSection c Y
  homInvId := (c.h.whiskerRight Y).congr (by
    apply NatTrans.ext
    funext n p
    rfl) (by
    apply NatTrans.ext
    funext n p
    rfl)
  invHomId := by
    apply SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq
    rw [pointSection_snd]

/-- The section is itself a raw homotopy equivalence of the exact original objects. -/
def sectionHomotopyEquiv {K : SSet.{u}} (c : K.Contractible) (Y : SSet.{u}) :
    SSet.HomotopyEquiv Y (K ⊗ Y) where
  hom := pointSection c Y
  inv := snd K Y
  homInvId := (projectionHomotopyEquiv c Y).invHomId
  invHomId := (projectionHomotopyEquiv c Y).homInvId

/-- Projection removes only the contractible parameter, without original fibrancy assumptions. -/
theorem projection_weakEquivalence {K : SSet.{u}} (c : K.Contractible) (Y : SSet.{u}) :
    WeakEquivalence (snd K Y) :=
  rawHomotopyEquiv_weakEquivalence (projectionHomotopyEquiv c Y)

/-- Inserting the supplied point is weak on the full original simplicial set. -/
theorem pointSection_weakEquivalence {K : SSet.{u}} (c : K.Contractible) (Y : SSet.{u}) :
    WeakEquivalence (pointSection c Y) :=
  rawHomotopyEquiv_weakEquivalence (sectionHomotopyEquiv c Y)

/-- Every original standard simplex may be removed as a weakly equivalent parameter. -/
theorem simplexProjection_weakEquivalence (n : ℕ) (Y : SSet.{u}) :
    WeakEquivalence (snd (Δ[n] : SSet.{u}) Y) :=
  projection_weakEquivalence (simplexContractible n) Y

end
end DaggerNativeContractibleSimplexParameter
