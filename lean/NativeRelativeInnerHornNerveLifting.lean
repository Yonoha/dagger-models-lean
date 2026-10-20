import NativeInnerHornRelativeExtension
import NativeInnerHornSimplexReconstruction

/-! The ORIGINAL coherent nerve preserves relative inner-horn lifting, with the supplied square. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
open DaggerOrdinaryRigidificationCof
open DaggerOrdinaryRigidificationCof.BoundaryData DaggerOrdinaryRigidificationCof.PathFacets
open DaggerOrdinaryRigidificationCof.InnerHornFaces
open DaggerNativeInnerHornFacePostcomposition
open DaggerNativeInnerHornDataPostcomposition
open DaggerNativeInnerHornRelativeExtension
open DaggerNativeInnerHornSimplexReconstruction
universe u
namespace DaggerNativeRelativeInnerHornNerveLifting
noncomputable section

theorem relative_functor_extension_eq {n : ℕ} {C B : SC.{u}} (k : interior n)
    (D : CompatibleFaceData (n + 1) C (Admissible k)) (p : C ⟶ B)
    (hp : Fibration (p.map (D.obj 0) (D.obj (Fin.last (n + 1)))))
    (D' : CompatibleFaceData (n + 1) B (Admissible k)) (he : post D p = D')
    (ellB : extremeHom.{u} n ⟶ (D'.obj 0 ⟶[SSet.{u}] D'.obj (Fin.last (n + 1))))
    (hB : (extremeHorn n k).ι ≫ ellB = InnerHornGlue.hornMap k D') :
    ∃ (ell : extremeHom.{u} n ⟶ (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
      (h : (extremeHorn n k).ι ≫ ell = InnerHornGlue.hornMap k D),
      InnerHornExtension.extensionFunctor k D ell h ≫ p =
        InnerHornExtension.extensionFunctor k D' ellB hB := by
  cases he
  exact relative_functor_extension k D p hp ellB hB

theorem relative_filling {n : ℕ} {C B : SC.{u}} (k : interior n) (p : C ⟶ B)
    (hp : ∀ x y : C.Obj, Fibration (p.map x y))
    (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ N.obj B)
    (sq : CommSq a (SSet.horn (n + 1) k.val).ι (N.map p) b) :
    ∃ c : (Δ[n + 1] : SSet.{u}) ⟶ N.obj C,
      (SSet.horn (n + 1) k.val).ι ≫ c = a ∧ c ≫ N.map p = b := by
  let G : T.obj ⦋n + 1⦌ ⟶ B := (SSet.yonedaEquiv b).down
  have hG : SSet.yonedaEquiv.symm (ULift.up G) = b :=
    SSet.yonedaEquiv.symm_apply_apply b
  have he : post (InnerHornData.data k a) p =
      InnerHornData.data k (restriction k G) := by
    rw [data_post]
    apply congrArg (InnerHornData.data k)
    exact sq.w.trans (congrArg (fun f ↦ (SSet.horn (n + 1) k.val).ι ≫ f) hG.symm)
  obtain ⟨ell, h, hcomp⟩ := relative_functor_extension_eq k (InnerHornData.data k a) p
    (hp _ _) (InnerHornData.data k (restriction k G)) he
    (G.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))))
    (hornMap_restriction k G).symm
  have hcomp' := hcomp.trans (extensionFunctor_restriction k G)
  let H := InnerHornExtension.extensionFunctor k (InnerHornData.data k a) ell h
  refine ⟨SSet.yonedaEquiv.symm (ULift.up H), ?_, ?_⟩
  · apply NatTrans.ext
    funext q s
    apply ULift.ext
    let φ : q.unop ⟶ ⦋n + 1⦌ := SSet.stdSimplex.objEquiv s.val
    have hmem : SubcomplexNerveData.Contains (SSet.horn.{u} (n + 1) k.val) φ := by
      simpa only [SubcomplexNerveData.Contains, φ,
        SSet.stdSimplex.objEquiv.symm_apply_apply] using s.property
    change T.map φ ≫ H = (a.app q s).down
    have hh := InnerHornNerveFiller.extensionFunctor_on_simplex k a ell h φ hmem
    have hs : (⟨SSet.stdSimplex.objEquiv.symm φ, hmem⟩ :
        (SSet.horn (n + 1) k.val).toSSet.obj q) = s :=
      Subtype.ext (SSet.stdSimplex.objEquiv.symm_apply_apply s.val)
    exact hh.trans (congrArg (fun t ↦ (a.app q t).down) hs)
  · rw [SSet.yonedaEquiv_symm_comp]
    change SSet.yonedaEquiv.symm (ULift.up (H ≫ p)) = b
    rw [hcomp']
    exact hG

theorem innerHorn_lifting {n : ℕ} {C B : SC.{u}} (k : interior n) (p : C ⟶ B)
    (hp : ∀ x y : C.Obj, Fibration (p.map x y)) :
    HasLiftingProperty (SSet.horn.{u} (n + 1) k.val).ι (N.map p) := by
  constructor
  intro a b sq
  obtain ⟨c, ha, hb⟩ := relative_filling k p hp a b sq
  exact ⟨c, ha, hb⟩

end
end DaggerNativeRelativeInnerHornNerveLifting
