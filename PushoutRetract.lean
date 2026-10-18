import Mathlib.CategoryTheory.MorphismProperty.RetractArgument
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

set_option autoImplicit false
set_option maxHeartbeats 0

open CategoryTheory Limits

universe v u
namespace DaggerCofibrationPushoutRetract
noncomputable section

variable {V : Type u} [Category.{v} V]
  {C C' B B' Z Z' : V}
  {f : C ⟶ C'} {i : C ⟶ B} {j : C' ⟶ B'} {f' : B ⟶ B'}
  {l : C ⟶ Z} {jZ : C' ⟶ Z'} {g : Z ⟶ Z'}
  (sq : IsPushout f i j f') (sqL : IsPushout f l jZ g)

/-- The original upper and lower cocones retain their full arbitrary-target UP. -/
theorem original_desc_unique {W : V} (h : C' ⟶ W) (k : B ⟶ W)
    (w : f ≫ h = i ≫ k) (d : B' ⟶ W)
    (hdj : j ≫ d = h) (hdf : f' ≫ d = k) : d = sq.desc h k w :=
  sq.hom_ext (hdj.trans (sq.inl_desc h k w).symm)
    (hdf.trans (sq.inr_desc h k w).symm)

theorem cell_desc_unique {W : V} (h : C' ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = l ≫ k) (d : Z' ⟶ W)
    (hdj : jZ ≫ d = h) (hdg : g ≫ d = k) : d = sqL.desc h k w :=
  sqL.hom_ext (hdj.trans (sqL.inl_desc h k w).symm)
    (hdg.trans (sqL.inr_desc h k w).symm)

def cobaseInclusion (r : B ⟶ Z) (hir : i ≫ r = l) : B' ⟶ Z' :=
  sq.desc jZ (r ≫ g) (by rw [← Category.assoc, hir, sqL.w])

def cobaseRetraction (p : Z ⟶ B) (fac : l ≫ p = i) : Z' ⟶ B' :=
  sqL.desc j (p ≫ f') (by rw [← Category.assoc, fac, sq.w])

@[reassoc (attr := simp)]
theorem original_left_inclusion (r : B ⟶ Z) (hir : i ≫ r = l) :
    j ≫ cobaseInclusion sq sqL r hir = jZ :=
  sq.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem original_right_inclusion (r : B ⟶ Z) (hir : i ≫ r = l) :
    f' ≫ cobaseInclusion sq sqL r hir = r ≫ g :=
  sq.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem cell_left_retraction (p : Z ⟶ B) (fac : l ≫ p = i) :
    jZ ≫ cobaseRetraction sq sqL p fac = j :=
  sqL.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem cell_right_retraction (p : Z ⟶ B) (fac : l ≫ p = i) :
    g ≫ cobaseRetraction sq sqL p fac = p ≫ f' :=
  sqL.inr_desc _ _ _

theorem cobaseInclusion_unique (r : B ⟶ Z) (hir : i ≫ r = l) (d : B' ⟶ Z')
    (hj : j ≫ d = jZ) (hf : f' ≫ d = r ≫ g) :
    d = cobaseInclusion sq sqL r hir :=
  original_desc_unique sq _ _ _ d hj hf

theorem cobaseRetraction_unique (p : Z ⟶ B) (fac : l ≫ p = i) (d : Z' ⟶ B')
    (hj : jZ ≫ d = j) (hg : g ≫ d = p ≫ f') :
    d = cobaseRetraction sq sqL p fac :=
  cell_desc_unique sqL _ _ _ d hj hg

theorem cobase_split (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (fac : l ≫ p = i) (hrp : r ≫ p = 𝟙 B) :
    cobaseInclusion sq sqL r hir ≫ cobaseRetraction sq sqL p fac = 𝟙 B' := by
  apply sq.hom_ext
  · simp
  · simp [← Category.assoc r p f', hrp]

/-- The actual supplied comparison, rather than an isomorphic replacement, is a retract. -/
def cobaseRetract (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (fac : l ≫ p = i) (hrp : r ≫ p = 𝟙 B) :
    RetractArrow f' g where
  i := Arrow.homMk r (cobaseInclusion sq sqL r hir)
    (original_right_inclusion sq sqL r hir).symm
  r := Arrow.homMk p (cobaseRetraction sq sqL p fac)
    (cell_right_retraction sq sqL p fac).symm
  retract := Arrow.hom_ext _ _ hrp (cobase_split sq sqL r p hir fac hrp)

@[simp] theorem cobaseRetract_i_left (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (fac : l ≫ p = i) (hrp : r ≫ p = 𝟙 B) :
    (cobaseRetract sq sqL r p hir fac hrp).i.left = r := rfl

@[simp] theorem cobaseRetract_i_right (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (fac : l ≫ p = i) (hrp : r ≫ p = 𝟙 B) :
    (cobaseRetract sq sqL r p hir fac hrp).i.right = cobaseInclusion sq sqL r hir := rfl

@[simp] theorem cobaseRetract_r_left (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (fac : l ≫ p = i) (hrp : r ≫ p = 𝟙 B) :
    (cobaseRetract sq sqL r p hir fac hrp).r.left = p := rfl

@[simp] theorem cobaseRetract_r_right (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (fac : l ≫ p = i) (hrp : r ≫ p = 𝟙 B) :
    (cobaseRetract sq sqL r p hir fac hrp).r.right = cobaseRetraction sq sqL p fac := rfl

end
end DaggerCofibrationPushoutRetract
