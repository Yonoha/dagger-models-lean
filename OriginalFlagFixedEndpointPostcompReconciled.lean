import OriginalFlagMappedCenterSupportReconciled

/-!
# Postcomposition with both fixed target endpoints

These wrappers reuse the original flag Hom map and its original Hom
naturality square. The two endpoint equalities are retained explicitly,
and raw representatives keep exactly the same necklace code and flag.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalFlagFixedEndpointPostcomp

noncomputable section

/-- The same degree object after postcomposition and specified endpoint equalities. -/
def fixedPostcompDegree {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = c) (hb : f.app (op ⦋0⦌) b = d)
    (n : ℕ) (p : Degree X a b n) : Degree Y c d n :=
  ⟨{ code := p.1.code
     map := p.1.map ≫ f
     first := by change f.app _ (p.1.map.app _ p.1.code.first) = c; rw [p.1.first, ha]
     last := by change f.app _ (p.1.map.app _ p.1.code.last) = d; rw [p.1.last, hb] }, p.2⟩

/-- The original flag Hom map with the prescribed target endpoint labels. -/
def fixedFlagHomMap {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = c) (hb : f.app (op ⦋0⦌) b = d) :
    flagHom X a b ⟶ flagHom Y c d := by
  subst c
  subst d
  exact flagHomMap f

/-- Quotient representatives retain their original code and flag under the endpoint wrappers. -/
theorem fixedFlagHomMap_class {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = c) (hb : f.app (op ⦋0⦌) b = d)
    (n : ℕ) (p : Degree X a b n) :
    (fixedFlagHomMap f a b c d ha hb).app (op ⦋n⦌) (classOf X a b n p) =
      classOf Y c d n (fixedPostcompDegree f a b c d ha hb n p) := by
  subst c
  subst d
  rfl

/-- The existing original Hom naturality square includes both fixed endpoint transports. -/
theorem fixedFlagHomMap_original_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = c) (hb : f.app (op ⦋0⦌) b = d) :
    fixedFlagHomMap f a b c d ha hb ≫ (flagOriginalHomIso Y c d).hom =
      (flagOriginalHomIso X a b).hom ≫
        (originalChosenHomMap f a b ≫
          targetHomTransport (congrArg (RV Y) ha) (congrArg (RV Y) hb)) := by
  subst c
  subst d
  change flagHomMap f ≫ (flagOriginalHomIso Y (f.app _ a) (f.app _ b)).hom =
    (flagOriginalHomIso X a b).hom ≫ originalChosenHomMap f a b
  exact flagOriginalHomIso_naturality f a b

end

end DaggerOriginalFlagFixedEndpointPostcomp
