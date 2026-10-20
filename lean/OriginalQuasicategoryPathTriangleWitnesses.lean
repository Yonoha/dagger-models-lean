import OriginalQuasicategoryEdgeHomotopyCategory

/-!
# Actual triangle witnesses for equations in the original path quotient

Use the native lift constructor from the original homotopy category into the
auxiliary edge-homotopy category. Its values on original edge classes recover
actual left homotopy triangles. An original inner tetrahedron filler then turns
an original composition equation into an actual CompStruct with all edges fixed.
The original path quotient, unit and core are unchanged, in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryTetrahedronFillers
open DaggerOriginalQuasicategoryEdgeHomotopies
open DaggerOriginalQuasicategoryEdgeHomotopyCategory

universe u

namespace DaggerOriginalQuasicategoryPathTriangleWitnesses

noncomputable section

/-- Test original path-quotient equations in auxiliary actual edge homotopy classes. -/
def pathToEdgeCategory {X : SSet.{u}} (hX : innerHornFillers X) :
    ((SSet.truncation 2).obj X).HomotopyCategory ⥤ EdgeHomotopyCategory X hX :=
  SSet.Truncated.HomotopyCategory.lift (V := (SSet.truncation 2).obj X)
    (EdgeHomotopyCategory.mk hX)
    (fun e ↦ EdgeHomotopyCategory.homMk hX (SSet.Edge.ofTruncated e))
    (EdgeHomotopyCategory.homMk_id hX)
    (fun t ↦ EdgeHomotopyCategory.homMk_comp hX (SSet.Edge.CompStruct.ofTruncated t))

/-- The comparison sends each exact original vertex to the same auxiliary vertex. -/
theorem pathToEdgeCategory_obj {X : SSet.{u}} (hX : innerHornFillers X)
    (x : X.obj (op ⦋0⦌)) :
    (pathToEdgeCategory hX).obj (SSet.Truncated.HomotopyCategory.mk x) =
      EdgeHomotopyCategory.mk hX x := rfl

/-- The comparison sends an original edge path class to the class of that same edge. -/
theorem pathToEdgeCategory_homMk {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    (pathToEdgeCategory hX).map (SSet.Truncated.HomotopyCategory.homMk e) =
      EdgeHomotopyCategory.homMk hX e := by
  exact SSet.Truncated.HomotopyCategory.lift_map_homMk
    (V := (SSet.truncation 2).obj X) (D := EdgeHomotopyCategory X hX)
    (EdgeHomotopyCategory.mk hX)
    (fun e ↦ EdgeHomotopyCategory.homMk hX (SSet.Edge.ofTruncated e))
    (EdgeHomotopyCategory.homMk_id hX)
    (fun t ↦ EdgeHomotopyCategory.homMk_comp hX (SSet.Edge.CompStruct.ofTruncated t))
    e.toTruncated

/-- Equality of original edge path classes is exactly an actual left homotopy triangle. -/
theorem original_homMk_eq_iff_leftHomotopic {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} :
    SSet.Truncated.HomotopyCategory.homMk f = SSet.Truncated.HomotopyCategory.homMk g ↔
      leftHomotopic f g := by
  constructor
  · intro h
    have hf := congrArg
      (fun k : SSet.Truncated.HomotopyCategory.mk x ⟶
        SSet.Truncated.HomotopyCategory.mk y ↦ (pathToEdgeCategory hX).map k) h
    change (pathToEdgeCategory hX).map (SSet.Truncated.HomotopyCategory.homMk f) =
      (pathToEdgeCategory hX).map (SSet.Truncated.HomotopyCategory.homMk g) at hf
    rw [pathToEdgeCategory_homMk, pathToEdgeCategory_homMk] at hf
    exact (EdgeHomotopyCategory.homMk_eq_iff_leftHomotopic hX).mp hf
  · rintro ⟨t⟩
    have h := SSet.Truncated.HomotopyCategory.homMk_comp_homMk t
    change SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (SSet.truncation 2).obj X) y) =
        SSet.Truncated.HomotopyCategory.homMk g at h
    simpa only [SSet.Truncated.HomotopyCategory.homMk_id, Category.comp_id] using h

/-- An original path-quotient composition equation admits the exact original triangle. -/
theorem original_compStruct_iff_path_fac {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)}
    {f : SSet.Edge x y} {g : SSet.Edge y z} {h : SSet.Edge x z} :
    Nonempty (f.CompStruct g h) ↔
      SSet.Truncated.HomotopyCategory.homMk f ≫
        SSet.Truncated.HomotopyCategory.homMk g =
          SSet.Truncated.HomotopyCategory.homMk h := by
  constructor
  · rintro ⟨t⟩
    exact SSet.Truncated.HomotopyCategory.homMk_comp_homMk t
  · intro fac
    have hfac := congrArg
      (fun k : SSet.Truncated.HomotopyCategory.mk x ⟶
        SSet.Truncated.HomotopyCategory.mk z ↦ (pathToEdgeCategory hX).map k) fac
    change (pathToEdgeCategory hX).map (SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g) =
        (pathToEdgeCategory hX).map (SSet.Truncated.HomotopyCategory.homMk h) at hfac
    rw [Functor.map_comp, pathToEdgeCategory_homMk, pathToEdgeCategory_homMk,
      pathToEdgeCategory_homMk] at hfac
    change EdgeHomotopyCategory.homMk hX (composeEdge hX f g) =
      EdgeHomotopyCategory.homMk hX h at hfac
    obtain ⟨t⟩ := (EdgeHomotopyCategory.homMk_eq_iff_leftHomotopic hX).mp hfac
    exact fill32 hX (compositionTriangle hX f g) (SSet.Edge.CompStruct.compId g) t

end

end DaggerOriginalQuasicategoryPathTriangleWitnesses
