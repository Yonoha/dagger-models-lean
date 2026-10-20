import OriginalJoinedSuffixFaceMaps

/-!
# Actual suffix horn maps by native multicoequalizer gluing

The original relative horn data supply maps on every suffix coface. Their
proved agreement on whole intersections makes a native multicofork, including
one-dimensional horns. Its native colimit constructs the map on the literal
suffix horn, with the exact original coface restriction equations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedSuffixFaceMaps

universe u

namespace DaggerOriginalJoinedSuffixHornGluing

noncomputable section

/-- The literal suffix horn is the native gluing of its actual suffix cofaces. -/
theorem suffixDiagram (k n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.MulticoequalizerDiagram (suffixHorn.{u} k (n + 1) i)
      (fun j : ({i}ᶜ : Set (Fin (n + 2))) ↦
        SSet.stdSimplex.face {suffixIndex k (n + 1) j.val}ᶜ)
      (fun j l ↦ SSet.stdSimplex.face {suffixIndex k (n + 1) j.val}ᶜ ⊓
        SSet.stdSimplex.face {suffixIndex k (n + 1) l.val}ᶜ) := ⟨rfl, fun _ _ ↦ rfl⟩

/-- The original coface maps form a native multicofork with every overlap equation proved. -/
def suffixHornCofork {X : SSet.{u}} (k n : ℕ) (i : Fin (n + 2))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X) :
    Multicofork ((suffixDiagram k n i).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun j ↦ suffixFaceMap k n i j.val j.property φ) (fun x ↦ by
    rcases x with ⟨⟨j, l⟩, hjl⟩
    change SSet.Subcomplex.homOfLE inf_le_left ≫ suffixFaceMap k n i j.val j.property φ =
      SSet.Subcomplex.homOfLE inf_le_right ≫ suffixFaceMap k n i l.val l.property φ
    cases n with
    | zero =>
      rcases j with ⟨j, hj⟩
      rcases l with ⟨l, hl⟩
      change j ≠ i at hj
      change l ≠ i at hl
      change j.val < l.val at hjl
      have hjv : j.val ≠ i.val := fun h ↦ hj (Fin.ext h)
      have hlv : l.val ≠ i.val := fun h ↦ hl (Fin.ext h)
      have hi := i.isLt
      have hbj := j.isLt
      have hbl := l.isLt
      exact False.elim (by omega)
    | succ n => exact suffixFaceMap_agreement k n i j.val l.val j.property l.property hjl φ)

/-- The actual map on the entire original suffix horn, constructed from the original horn data. -/
def suffixHornMap {X : SSet.{u}} (k n : ℕ) (i : Fin (n + 2))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X) :
    (suffixHorn k (n + 1) i : SSet.{u}) ⟶ X :=
  (suffixDiagram k n i).isColimit'.desc (suffixHornCofork k n i φ)

/-- Restriction to each actual suffix face is exactly the original coface map. -/
theorem suffixHornMap_face {X : SSet.{u}} (k n : ℕ) (i : Fin (n + 2))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X)
    (j : ({i}ᶜ : Set (Fin (n + 2)))) :
    SSet.Subcomplex.homOfLE (le_iSup (fun a : ({i}ᶜ : Set (Fin (n + 2))) ↦
      SSet.stdSimplex.face {suffixIndex k (n + 1) a.val}ᶜ) j) ≫ suffixHornMap k n i φ =
      suffixFaceMap k n i j.val j.property φ :=
  (suffixDiagram k n i).isColimit'.fac (suffixHornCofork k n i φ) (.right j)

end

end DaggerOriginalJoinedSuffixHornGluing
