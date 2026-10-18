import OriginalCounitRightConeQCommonConeImageReconciled
import OriginalCounitRightConeQCommonBaseRetractionFactorReconciled
import OriginalCounitRightConeQSupportedRetractionReconciled
import OriginalCounitRightConeQCenterSupportReconciled
import OriginalCounitRightConeQFunctorReconciled

/-!
# Lift a supported original flagged necklace through the common cone

The explicit common face has a simplex-category retraction. Its actual
cone map therefore has a retraction. A supported necklace map can be
postcomposed with that retraction; the full map recovers exactly under
the common cone map, while its original code and flag are unchanged.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCommonBaseRetractionFactor
open DaggerOriginalCounitRightConeQSupportedRetraction
open DaggerChosenRigidificationNecklace
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalCounitRightConeQCommonCenterLift

noncomputable section

/-- The chosen actual monotone retraction of the common old face. -/
def commonRetraction (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    ⦋n + 2⦌ ⟶ ⦋n⦌ :=
  Classical.choose (commonBaseHom_has_retraction n i j hij)

theorem commonRetraction_spec (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    commonBaseHom n i j hij ≫ commonRetraction n i j hij = 𝟙 ⦋n⦌ :=
  Classical.choose_spec (commonBaseHom_has_retraction n i j hij)

/-- Retraction of the original literal cone map. -/
theorem commonConeRetraction_spec (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    coneMap.{u} (commonBaseHom n i j hij) ≫
      coneMap.{u} (commonRetraction n i j hij) =
        𝟙 (cone.{u} n) := by
  calc
    coneMap.{u} (commonBaseHom n i j hij) ≫
        coneMap.{u} (commonRetraction n i j hij) =
      coneFunctor.{u}.map
        (commonBaseHom n i j hij ≫ commonRetraction n i j hij) :=
        (coneFunctor.{u}.map_comp _ _).symm
    _ = coneFunctor.{u}.map (𝟙 ⦋n⦌) := by rw [commonRetraction_spec]
    _ = 𝟙 (cone.{u} n) := coneFunctor.{u}.map_id ⦋n⦌

/-- Lift the *same original code and flag* of a supported degree object
from the target cone to the actual smaller common cone. -/
def supportedDegreeLift (n d : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j)
    (p : Degree (cone.{u} (n + 2)) (alpha.{u} (n + 2))
      (omega.{u} (n + 2)) d)
    (hp : SSet.Subcomplex.range p.1.map ≤
      SSet.Subcomplex.range (coneMap.{u} (commonBaseHom n i j hij))) :
    Degree (cone.{u} n) (alpha.{u} n) (omega.{u} n) d :=
  ⟨{ code := p.1.code
     map := p.1.map ≫ coneMap.{u} (commonRetraction n i j hij)
     first := by
       change (coneMap.{u} (commonRetraction n i j hij)).app (op ⦋0⦌)
         (p.1.map.app (op ⦋0⦌) p.1.code.first) = alpha.{u} n
       have hsplit := commonConeRetraction_spec.{u} n i j hij
       have hinj : Function.Injective
           ((coneMap.{u} (commonBaseHom n i j hij)).app (op ⦋0⦌)) :=
         Function.LeftInverse.injective
           (fun z ↦ congrFun (NatTrans.congr_app hsplit (op ⦋0⦌)) z)
       apply hinj
       have hfix := supported_map_fixed_of_split
         (coneMap.{u} (commonBaseHom n i j hij))
         (coneMap.{u} (commonRetraction n i j hij)) hsplit p.1.map hp
       have hf := congrFun (NatTrans.congr_app hfix (op ⦋0⦌)) p.1.code.first
       change (coneMap.{u} (commonBaseHom n i j hij)).app (op ⦋0⦌)
         ((coneMap.{u} (commonRetraction n i j hij)).app (op ⦋0⦌)
           (p.1.map.app (op ⦋0⦌) p.1.code.first)) =
             p.1.map.app (op ⦋0⦌) p.1.code.first at hf
       rw [hf, p.1.first]
       exact (alpha_naturality (commonBaseHom n i j hij)).symm
     last := by
       change (coneMap.{u} (commonRetraction n i j hij)).app (op ⦋0⦌)
         (p.1.map.app (op ⦋0⦌) p.1.code.last) = omega.{u} n
       rw [p.1.last]
       exact omega_naturality (commonRetraction n i j hij) }, p.2⟩

/-- The lifted whole necklace map recovers the original map exactly. -/
theorem supportedDegreeLift_map (n d : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j)
    (p : Degree (cone.{u} (n + 2)) (alpha.{u} (n + 2))
      (omega.{u} (n + 2)) d)
    (hp : SSet.Subcomplex.range p.1.map ≤
      SSet.Subcomplex.range (coneMap.{u} (commonBaseHom n i j hij))) :
    (supportedDegreeLift n d i j hij p hp).1.map ≫
      coneMap.{u} (commonBaseHom n i j hij) = p.1.map := by
  change (p.1.map ≫ coneMap.{u} (commonRetraction n i j hij)) ≫
    coneMap.{u} (commonBaseHom n i j hij) = p.1.map
  exact supported_map_fixed_of_split
    (coneMap.{u} (commonBaseHom n i j hij))
    (coneMap.{u} (commonRetraction n i j hij))
    (commonConeRetraction_spec.{u} n i j hij) p.1.map hp

/-- No flag recoding occurs in the supported degree lift. -/
theorem supportedDegreeLift_flag (n d : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j)
    (p : Degree (cone.{u} (n + 2)) (alpha.{u} (n + 2))
      (omega.{u} (n + 2)) d)
    (hp : SSet.Subcomplex.range p.1.map ≤
      SSet.Subcomplex.range (coneMap.{u} (commonBaseHom n i j hij))) :
    (supportedDegreeLift n d i j hij p hp).2 = p.2 := rfl

end

end DaggerOriginalCounitRightConeQCommonCenterLift
