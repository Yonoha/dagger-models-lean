import OriginalInnerHornExtensionFaces
import OriginalSubcomplexSimplexRestriction
import OriginalInnerHornData

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornNerveFiller

noncomputable section

open BoundaryData PathFacets InnerHornFaces

variable {n : ℕ} {A : SC.{u}} (k : interior n)
variable (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj A)
variable (ell : extremeHom.{u} n ⟶
  ((InnerHornData.data k a).obj 0 ⟶[SSet.{u}]
    (InnerHornData.data k a).obj (Fin.last (n + 1))))
variable (hl : (extremeHorn n k).ι ≫ ell =
  InnerHornGlue.hornMap k (InnerHornData.data k a))

include hl in
/-- Restriction to every simplex actually contained in the supplied original horn. -/
theorem extensionFunctor_on_simplex {m : SimplexCategory} (φ : m ⟶ ⦋n + 1⦌)
    (hmem : SubcomplexNerveData.Contains (SSet.horn.{u} (n + 1) k.val) φ) :
    T.map φ ≫ InnerHornExtension.extensionFunctor k (InnerHornData.data k a) ell hl =
      SubcomplexNerveData.simplex (SSet.horn (n + 1) k.val) a φ hmem := by
  obtain ⟨r, hrk, hr⟩ := (InnerHornData.contains_iff_omits k φ).mp hmem
  let s := missingFace r
  have hφ : ∀ i, φ.toOrderHom i ∈ s := fun i ↦ (mem_missingFace r _).mpr (hr i)
  have hs : s.Nonempty := ⟨φ.toOrderHom 0, hφ 0⟩
  have hp : Admissible k s := ⟨r, hrk, fun h ↦ (mem_missingFace r r).mp h rfl⟩
  have hf : SimplicialThickening.functor φ.toOrderHom.uliftMap =
      EnrichedFunctor.comp SSet
        (SimplicialThickening.functor (faceLift s φ hφ).uliftMap)
        (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom) := by
    rw [← SimplicialThickening.functor_comp]
    rfl
  have hface := InnerHornExtensionFaces.extensionFunctor_on_face
    k (InnerHornData.data k a) ell hl s hs hp
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (InnerHornExtension.extensionFunctor k (InnerHornData.data k a) ell hl) =
        (InnerHornData.data k a).canonicalF s hs hp at hface
  change EnrichedFunctor.comp SSet (SimplicialThickening.functor φ.toOrderHom.uliftMap)
    (InnerHornExtension.extensionFunctor k (InnerHornData.data k a) ell hl) = _
  rw [hf]
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (faceLift s φ hφ).uliftMap)
    (EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom)
      (InnerHornExtension.extensionFunctor k (InnerHornData.data k a) ell hl)) = _
  rw [hface, InnerHornData.data_canonicalF]
  exact SubcomplexNerveData.simplex_from_face (SSet.horn (n + 1) k.val) a s hs
    ((faceOrdinal_mem_iff k s hs).mpr hp) φ hφ hmem

/-- The original coherent nerve fills every inner horn when all target Homs are Kan. -/
theorem innerHorn_filling (hKan : ∀ x y : A.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    ∃ b : Δ[n + 1] ⟶ N.obj A, (SSet.horn (n + 1) k.val).ι ≫ b = a := by
  let D := InnerHornData.data k a
  letI := hKan (D.obj 0) (D.obj (Fin.last (n + 1)))
  obtain ⟨ell, hl⟩ := InnerHornGlue.exists_extension k D
  let H := InnerHornExtension.extensionFunctor k D ell hl
  refine ⟨SSet.yonedaEquiv.symm (ULift.up H), ?_⟩
  apply NatTrans.ext
  funext q s
  apply ULift.ext
  let φ : q.unop ⟶ ⦋n + 1⦌ := SSet.stdSimplex.objEquiv s.val
  have hmem : SubcomplexNerveData.Contains (SSet.horn (n + 1) k.val) φ := by
    simpa only [SubcomplexNerveData.Contains, φ,
      SSet.stdSimplex.objEquiv.symm_apply_apply] using s.property
  change T.map φ ≫ H = (a.app q s).down
  have h := extensionFunctor_on_simplex k a ell hl φ hmem
  have hs : (⟨SSet.stdSimplex.objEquiv.symm φ, hmem⟩ :
      (SSet.horn (n + 1) k.val).toSSet.obj q) = s :=
    Subtype.ext (SSet.stdSimplex.objEquiv.symm_apply_apply s.val)
  exact h.trans (congrArg (fun t ↦ (a.app q t).down) hs)

end

end DaggerOrdinaryRigidificationCof.InnerHornNerveFiller
