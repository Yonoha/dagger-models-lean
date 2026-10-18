import NativeHorizontalPiCompatibility
import NativeGeometricTotalPiFunctor

/-! Compatible original row pi classes are exactly sections over the original vertex map. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open SSet.KanComplex DaggerNativeBisimplicialHorizontalMapping
open DaggerNativeHorizontalPiCompatibility DaggerNativeTotalBasedPiFunctor
open DaggerNativeGeometricTotalPiFunctor
universe u
namespace DaggerNativeHorizontalPiSections
noncomputable section

def vertexMap (K : SSet.{u}) (X : BiSSet.{u})
    (a : (horizontalMapping K X) _⦋0⦌) :
    K ⟶ X ⋙ SSet.evaluation.obj (op ⦋0⦌) := a

def rowProjection (X : BiSSet.{u}) (t : ℕ) :
    X ⋙ totalPiFunctor t ⟶ X ⋙ SSet.evaluation.obj (op ⦋0⦌) :=
  Functor.whiskerLeft X (vertexProjection t)

def PiSection (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) :=
  {f : K ⟶ X ⋙ totalPiFunctor t // f ≫ rowProjection X t = vertexMap K X a}

def familyMap (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) (s : CompatiblePiFamily K X t a) :
    K ⟶ X ⋙ totalPiFunctor t where
  app d x := ⟨a.app d x, s.val d x⟩
  naturality d e α := by
    funext x
    exact ((congrArg (fun z ↦ (⟨a.app e (K.map α x), z⟩ :
      Σ y : (X.obj e) _⦋0⦌, π t (X.obj e) y)) (s.property d e α x)).symm).trans
        (sigma_mapπ_target (X.map α) t _ _ (basepoint_horizontal K X a α x) _)

def familySection (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) :
    CompatiblePiFamily K X t a → PiSection K X t a :=
  fun s ↦ ⟨familyMap K X t a s, rfl⟩

def sigmaFibreEquiv {A : Type u} (P : A → Type u) (a : A) :
    {z : Sigma P // z.1 = a} ≃ P a where
  toFun z := z.property ▸ z.val.2
  invFun p := ⟨⟨a, p⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b, p⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

def sectionValue (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) (f : PiSection K X t a)
    (d : SimplexCategoryᵒᵖ) (x : K.obj d) : π t (X.obj d) (a.app d x) :=
  sigmaFibreEquiv (fun y ↦ π t (X.obj d) y) (a.app d x)
    ⟨f.val.app d x, congrFun (NatTrans.congr_app f.property d) x⟩

theorem sectionValue_pair (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) (f : PiSection K X t a)
    (d : SimplexCategoryᵒᵖ) (x : K.obj d) :
    (⟨a.app d x, sectionValue K X t a f d x⟩ :
      Σ y : (X.obj d) _⦋0⦌, π t (X.obj d) y) = f.val.app d x := by
  exact congrArg Subtype.val ((sigmaFibreEquiv (fun y ↦ π t (X.obj d) y)
    (a.app d x)).symm_apply_apply
      ⟨f.val.app d x, congrFun (NatTrans.congr_app f.property d) x⟩)

def sectionFamily (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) :
    PiSection K X t a → CompatiblePiFamily K X t a := fun f ↦
  ⟨sectionValue K X t a f, by
    intro d e α x
    apply eq_of_heq
    apply (Sigma.mk.inj ?_).2
    calc
      (⟨a.app e (K.map α x), mapπ (X.map α) t _ _
          (basepoint_horizontal K X a α x) (sectionValue K X t a f d x)⟩ :
          Σ y : (X.obj e) _⦋0⦌, π t (X.obj e) y) =
          (totalPiFunctor t).map (X.map α)
            ⟨a.app d x, sectionValue K X t a f d x⟩ :=
        sigma_mapπ_target (X.map α) t _ _ _ _
      _ = (totalPiFunctor t).map (X.map α) (f.val.app d x) := by
        rw [sectionValue_pair]
      _ = f.val.app e (K.map α x) := (congrFun (f.val.naturality α) x).symm
      _ = ⟨a.app e (K.map α x), sectionValue K X t a f e (K.map α x)⟩ :=
        (sectionValue_pair K X t a f e (K.map α x)).symm⟩

def familySectionEquiv (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) :
    CompatiblePiFamily K X t a ≃ PiSection K X t a where
  toFun := familySection K X t a
  invFun := sectionFamily K X t a
  left_inv s := by
    apply Subtype.ext
    funext d x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply NatTrans.ext
    funext d x
    exact sectionValue_pair K X t a f d x

end
end DaggerNativeHorizontalPiSections
