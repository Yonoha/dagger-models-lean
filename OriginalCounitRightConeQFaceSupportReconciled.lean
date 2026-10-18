import OriginalCounitRightConeQBoundaryFaceOverlapReconciled
import OriginalFlagFlankedCodeEpi

/-!
# Support of flanked Q-face representatives under necklace arrows

An over-cone triangle alone does not show that a target necklace remains in
a given coface. For flanked flags, the retained code-map epi theorem makes
the triangle pointwise surjective, so its full simplicial-set image stays
inside the original coface image. This is a concrete support step toward
the outstanding two-face overlap theorem.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode
open DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor

universe u

namespace DaggerOriginalCounitRightConeQFaceSupport

noncomputable section

/-- An epi code arrow and an over-X triangle preserve image-subcomplex support. -/
theorem support_descends_of_epi {X : SSet.{u}}
    {a b : X.obj (op ⦋0⦌)} {P R : NecklacesOver X a b}
    (h : P ⟶ R) [Epi h.hom.map] (A : X.Subcomplex)
    (hP : SSet.Subcomplex.range P.map ≤ A) :
    SSet.Subcomplex.range R.map ≤ A := by
  have heq : SSet.Subcomplex.range R.map = SSet.Subcomplex.range P.map := by
    have hcode : SSet.Subcomplex.range h.hom.map = ⊤ :=
      SSet.Subcomplex.range_eq_top h.hom.map
    calc
      SSet.Subcomplex.range R.map =
          (⊤ : R.code.toSSet.Subcomplex).image R.map :=
        (SSet.Subcomplex.image_top R.map).symm
      _ = (SSet.Subcomplex.range h.hom.map).image R.map := by rw [hcode]
      _ = SSet.Subcomplex.range (h.hom.map ≫ R.map) :=
        (SSet.Subcomplex.range_comp h.hom.map R.map).symm
      _ = SSet.Subcomplex.range P.map := by rw [h.w]
  rw [heq]
  exact hP

/-- The retained all-degree flanked-code epi supplies actual support descent. -/
theorem flanked_support_descends {X : SSet.{u}}
    {a b : X.obj (op ⦋0⦌)} {P R : NecklacesOver X a b} {n : ℕ}
    (F : Flag.{u} P.code n) (G : Flag.{u} R.code n)
    (h : P ⟶ R) (hFG : NecklaceCode.Flag.map h.hom F = G)
    (hF : Flanked F) (hG : Flanked G) (A : X.Subcomplex)
    (hP : SSet.Subcomplex.range P.map ≤ A) :
    SSet.Subcomplex.range R.map ≤ A := by
  letI : Epi h.hom.map := flanked_code_epi F G h.hom hFG hF hG
  exact support_descends_of_epi h A hP

/-- Every flanked necklace arrow starting in a literal Q coface keeps its
target's whole simplicial image inside that coface's image subcomplex. -/
theorem coface_support_descends (k : ℕ) (i : Fin (k + 2)) {n : ℕ}
    (P : NecklacesOver (cone.{u} k) (alpha.{u} k) (omega.{u} k))
    (R : NecklacesOver (cone.{u} (k + 1))
      ((coneMap.{u} (SimplexCategory.δ i)).app (op ⦋0⦌) (alpha.{u} k))
      ((coneMap.{u} (SimplexCategory.δ i)).app (op ⦋0⦌) (omega.{u} k)))
    (F : Flag.{u} P.code n) (G : Flag.{u} R.code n)
    (h : ((NecklacesOver.postcomp (coneMap.{u} (SimplexCategory.δ i))).obj P) ⟶ R)
    (hFG : NecklaceCode.Flag.map h.hom F = G)
    (hF : Flanked F) (hG : Flanked G) :
    SSet.Subcomplex.range R.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) := by
  letI : Epi h.hom.map := flanked_code_epi F G h.hom hFG hF hG
  have hP : SSet.Subcomplex.range
      (((NecklacesOver.postcomp
        (coneMap.{u} (SimplexCategory.δ i))).obj P).map) ≤
        SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) := by
    change SSet.Subcomplex.range (P.map ≫ coneMap.{u} (SimplexCategory.δ i)) ≤ _
    exact Subfunctor.range_comp_le _ _
  exact support_descends_of_epi
    (P := (NecklacesOver.postcomp
      (coneMap.{u} (SimplexCategory.δ i))).obj P) (R := R) h _ hP

/-- A common flanked target of two face-supported representatives has its
entire simplicial image in the intersection of the literal cone cofaces. -/
theorem two_coface_common_target_support (k : ℕ) (i j : Fin (k + 2)) {n : ℕ}
    (P S R : NecklacesOver (cone.{u} (k + 1)) (alpha.{u} (k + 1))
      (omega.{u} (k + 1)))
    (F : Flag.{u} P.code n) (H : Flag.{u} S.code n)
    (G : Flag.{u} R.code n)
    (f : P ⟶ R) (g : S ⟶ R)
    (hf : NecklaceCode.Flag.map f.hom F = G)
    (hg : NecklaceCode.Flag.map g.hom H = G)
    (hF : Flanked F) (hH : Flanked H) (hG : Flanked G)
    (hPi : SSet.Subcomplex.range P.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)))
    (hSj : SSet.Subcomplex.range S.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j))) :
    SSet.Subcomplex.range R.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) ⊓
        SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j)) := by
  exact le_inf
    (flanked_support_descends F G f hf hF hG _ hPi)
    (flanked_support_descends H G g hg hH hG _ hSj)

/-- The preceding support statement is an actual map into the intersection
subcomplex, before identifying that intersection with boundary Q data. -/
def two_coface_common_target_lift (k : ℕ) (i j : Fin (k + 2)) {n : ℕ}
    (P S R : NecklacesOver (cone.{u} (k + 1)) (alpha.{u} (k + 1))
      (omega.{u} (k + 1)))
    (F : Flag.{u} P.code n) (H : Flag.{u} S.code n)
    (G : Flag.{u} R.code n)
    (f : P ⟶ R) (g : S ⟶ R)
    (hf : NecklaceCode.Flag.map f.hom F = G)
    (hg : NecklaceCode.Flag.map g.hom H = G)
    (hF : Flanked F) (hH : Flanked H) (hG : Flanked G)
    (hPi : SSet.Subcomplex.range P.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)))
    (hSj : SSet.Subcomplex.range S.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j))) :
    R.code.toSSet ⟶
      ((SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) ⊓
        SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j)) :
          (cone.{u} (k + 1)).Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.lift R.map
    (two_coface_common_target_support k i j P S R F H G f g hf hg
      hF hH hG hPi hSj)

theorem two_coface_common_target_lift_ι (k : ℕ) (i j : Fin (k + 2)) {n : ℕ}
    (P S R : NecklacesOver (cone.{u} (k + 1)) (alpha.{u} (k + 1))
      (omega.{u} (k + 1)))
    (F : Flag.{u} P.code n) (H : Flag.{u} S.code n)
    (G : Flag.{u} R.code n)
    (f : P ⟶ R) (g : S ⟶ R)
    (hf : NecklaceCode.Flag.map f.hom F = G)
    (hg : NecklaceCode.Flag.map g.hom H = G)
    (hF : Flanked F) (hH : Flanked H) (hG : Flanked G)
    (hPi : SSet.Subcomplex.range P.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)))
    (hSj : SSet.Subcomplex.range S.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j))) :
    two_coface_common_target_lift.{u} k i j P S R F H G f g hf hg
        hF hH hG hPi hSj ≫
      (SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) ⊓
        SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j))).ι = R.map :=
  SSet.Subcomplex.lift_ι _ _

end

end DaggerOriginalCounitRightConeQFaceSupport
