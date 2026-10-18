import OriginalCoreLeftMappingFullComparison
import OriginalFullVertexPointedHomotopyComparison
import OriginalLeftMappingFullFaithfulness

/-!
# Positive homotopy comparison for the actual original-core mapping inclusion

The actual inclusion is the full-subcomplex inclusion after the proved literal
simplicial isomorphism. The existing original full-subcomplex theorem therefore
makes its native positive pointed homotopy maps bijective. All basepoint maps
are retained through the exact commuting inclusion equation.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryCoreKan DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalLeftMappingCoreSubcomplex DaggerOriginalFullVertexSubcomplex
open DaggerOriginalFullVertexPointedHomotopyComparison
open DaggerOriginalCoreLeftMappingFullComparison

universe u

namespace DaggerOriginalCoreLeftMappingHomotopyComparison

noncomputable section

/-- Bijectivity of a native pointed homotopy map is invariant under an actual arrow equality.
-/
theorem mapπ_bijective_congr {K L : SSet.{u}} {f g : K ⟶ L} (hfg : f = g)
    {n : ℕ} {x : K.obj (op ⦋0⦌)} {y : L.obj (op ⦋0⦌)} (hxy : f.app (op ⦋0⦌) x = y)
    (hbij : Function.Bijective (SSet.KanComplex.mapπ f n x y hxy)) :
    Function.Bijective (SSet.KanComplex.mapπ g n x (g.app (op ⦋0⦌) x) rfl) := by
  subst g
  subst y
  exact hbij

/-- The actual original-core mapping inclusion is bijective on every positive pointed homotopy
 group. -/
theorem coreMappingInclusion_mapπ_positive_bijective (X : SSet.{u})
    (hX : innerHornFillers X)
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)) (n : ℕ)
    (v : (leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b).obj (op ⦋0⦌)) :
    Function.Bijective (SSet.KanComplex.mapπ (coreMappingInclusion X a b) (n + 1) v
      ((coreMappingInclusion X a b).app (op ⦋0⦌) v) rfl) := by
  haveI : (leftMappingSpace X a.val b.val).KanComplex := leftMappingSpace_kan hX _ _
  let e := coreMappingFullIso X a b
  let u := e.hom.app (op ⦋0⦌) v
  have hiso : Function.Bijective (SSet.KanComplex.mapπ e.hom (n + 1) v u rfl) :=
    (SSet.KanComplex.mapπEquivOfIso e (n + 1) v u rfl).bijective
  have hfull := inclusion_mapπ_positive_bijective (equivalenceVertexSet X a.val b.val) u n
  have hcomp := hfull.comp hiso
  rw [SSet.KanComplex.mapπ_comp_mapπ] at hcomp
  change Function.Bijective (SSet.KanComplex.mapπ
    ((coreMappingFullIso X a b).hom ≫
      (fullVertexSubcomplex (leftMappingSpace X a.val b.val)
        (equivalenceVertexSet X a.val b.val)).ι) (n + 1) v u.val _) at hcomp
  exact mapπ_bijective_congr (coreMappingFullIso_hom_ι X a b) _ hcomp

end

end DaggerOriginalCoreLeftMappingHomotopyComparison
