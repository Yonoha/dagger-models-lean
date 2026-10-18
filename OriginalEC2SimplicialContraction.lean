import OriginalEC2SimplicialAction
import NerveHomotopy
import TopCatModelCategory.SSet.Contractible

/-!
# The actual simplicial contraction of the codiscrete two-element nerve

The constant-to-identity natural transformation is taken in the literal
codiscrete category. This is a simplicial contraction, not a claim about
free or contractible topological realizations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction

universe u

namespace DaggerOriginalEC2SimplicialContraction

noncomputable section

private abbrev B : Type u := Codiscrete C2.{u}

/-- The object labelled by the identity of the actual acting group. -/
def point : B.{u} := Codiscrete.mk (1 : C2.{u})

/-- The literal constant endofunctor at that object. -/
def constantFunctor : B.{u} ⥤ B.{u} := (Functor.const B.{u}).obj point.{u}

/-- The whole nerve map of the constant functor is the chosen constant map. -/
theorem nerveMap_constantFunctor :
    nerveMap constantFunctor.{u} =
      SSet.const (ComposableArrows.mk₀ point.{u}) := by
  letI : Quiver.IsThin B.{u} := by
    intro a b
    change Subsingleton Unit
    infer_instance
  apply NatTrans.ext
  funext n x
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- Every codiscrete object has its unique arrow from the chosen object. -/
def contractionNatTrans : constantFunctor.{u} ⟶ 𝟭 B.{u} := Codiscrete.natTrans

/-- The actual natural transformation contracts the codiscrete nerve. -/
def contraction : SSet.Homotopy
    (SSet.const (ComposableArrows.mk₀ point.{u}))
    (𝟙 simplicialEC2.{u}) := by
  have hid : nerveMap (𝟭 B.{u}) = 𝟙 simplicialEC2.{u} :=
    nerveFunctor.map_id (Cat.of B.{u})
  exact (DaggerNerveHomotopy.natTransHomotopy contractionNatTrans.{u}).congr
    nerveMap_constantFunctor.{u} hid

/-- The manuscript's actual simplicial $E_\bullet C_2$ is contractible. -/
def simplicialEC2Contractible : SSet.Contractible simplicialEC2.{u} where
  pt := ComposableArrows.mk₀ point.{u}
  h := contraction.{u}

end

end DaggerOriginalEC2SimplicialContraction
