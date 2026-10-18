import FixedCategoryColimits
import FixedCategoryFilteredDomains
import DaggerModels.SmallObjectFiniteDomains

/-! Small object arguments for the literal original fixed-category I and J.
Each family has one chosen full Arrow factorization functor. Its induced map
factorizations and the semantic-right copies retain the same actual Z, i and p.
No cell acyclicity or fixed-category model structure is asserted. -/

open CategoryTheory Limits MorphismProperty DaggerModels
open DaggerFixedCategoryGenerators

universe u

namespace DaggerFixedCategorySmallObject

noncomputable section

variable (O : Type u)

theorem I_hasSmallObjectArgument : HasSmallObjectArgument.{u} (I O) := by
  letI := I_isSmall O
  exact SmallObjectFiniteDomains.hasSmallObjectArgument.{u} (I O)
    (DaggerFixedCategoryFilteredDomains.I_domain_isFinitelyPresentable O)

theorem J_hasSmallObjectArgument : HasSmallObjectArgument.{u} (J O) := by
  letI := J_isSmall O
  exact SmallObjectFiniteDomains.hasSmallObjectArgument.{u} (J O)
    (DaggerFixedCategoryFilteredDomains.J_domain_isFinitelyPresentable O)

theorem I_hasFunctorialFactorization : HasFunctorialFactorization (I O).rlp.llp (I O).rlp := by
  letI := I_hasSmallObjectArgument O
  infer_instance

theorem J_hasFunctorialFactorization : HasFunctorialFactorization (J O).rlp.llp (J O).rlp := by
  letI := J_hasSmallObjectArgument O
  infer_instance

def I_functorialFactorizationData : FunctorialFactorizationData (I O).rlp.llp (I O).rlp := by
  letI := I_hasFunctorialFactorization O
  exact functorialFactorizationData _ _

def J_functorialFactorizationData : FunctorialFactorizationData (J O).rlp.llp (J O).rlp := by
  letI := J_hasFunctorialFactorization O
  exact functorialFactorizationData _ _

def I_mapFactorizationData {A B : FixedDaggerSimplicialCat O} (f : A ⟶ B) :
    MapFactorizationData (I O).rlp.llp (I O).rlp f :=
  (I_functorialFactorizationData O).factorizationData f

def J_mapFactorizationData {A B : FixedDaggerSimplicialCat O} (f : A ⟶ B) :
    MapFactorizationData (J O).rlp.llp (J O).rlp f :=
  (J_functorialFactorizationData O).factorizationData f

def I_semanticFactorizationData : FunctorialFactorizationData (I O).rlp.llp (F O ⊓ W O) :=
  (I_functorialFactorizationData O).ofLE le_rfl (I_rlp_eq O).le

def J_semanticFactorizationData : FunctorialFactorizationData (J O).rlp.llp (F O) :=
  (J_functorialFactorizationData O).ofLE le_rfl (J_rlp_eq O).le

@[simp] theorem I_semantic_Z :
    (I_semanticFactorizationData O).Z = (I_functorialFactorizationData O).Z := rfl

@[simp] theorem I_semantic_i :
    (I_semanticFactorizationData O).i = (I_functorialFactorizationData O).i := rfl

@[simp] theorem I_semantic_p :
    (I_semanticFactorizationData O).p = (I_functorialFactorizationData O).p := rfl

@[simp] theorem J_semantic_Z :
    (J_semanticFactorizationData O).Z = (J_functorialFactorizationData O).Z := rfl

@[simp] theorem J_semantic_i :
    (J_semanticFactorizationData O).i = (J_functorialFactorizationData O).i := rfl

@[simp] theorem J_semantic_p :
    (J_semanticFactorizationData O).p = (J_functorialFactorizationData O).p := rfl

end

end DaggerFixedCategorySmallObject
