import OriginalDaggerFreeComparisonRecovered
import OriginalOrdinaryFreeDaggerRecovered

/-! Original free comparison, recovered with its unchanged typed construction and proof terms. -/

set_option autoImplicit false
set_option maxRecDepth 100000
open DaggerModels.OrdinaryRigidification.DaggerAdjunction
open DaggerModels.OrdinaryRigidification.DaggerFreeComparison

noncomputable def
  DaggerModels.OrdinaryRigidification.DaggerFreeComparison.canonicalFreeComparison.{
    u
  } :
  @CategoryTheory.Iso.{u + 1, u + 1}
    (@CategoryTheory.Functor.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
    (@CategoryTheory.Functor.category.{u, u, u + 1, u + 1} _root_.SSet.{u}
      SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
    (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
      SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
      DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
      DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
    (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
      SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
      DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
      DaggerModels.OrdinaryRigidification.rigidification.{u}
      DaggerModels.OrdinaryFreeDagger.functor.{u})
:=
  @freeComparison.{u}
    DaggerModels.OrdinaryFreeDagger.functor.{u} DaggerModels.OrdinaryFreeDagger.adjunction.{u}

noncomputable def
  DaggerModels.OrdinaryRigidification.DaggerFreeComparison.canonicalTargetAdjunction.{
    u
  } :
  @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
    DaggerModels.DaggerSimplicialCat.{u, u} DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
    (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
      SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
      DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
      DaggerModels.OrdinaryRigidification.rigidification.{u}
      DaggerModels.OrdinaryFreeDagger.functor.{u})
    (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
      DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
      DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.forget.{u, u}
      DaggerModels.OrdinaryRigidification.coherentNerve.{u})
:=
  @targetAdjunction.{u}
    DaggerModels.OrdinaryFreeDagger.functor.{u} DaggerModels.OrdinaryFreeDagger.adjunction.{u}

theorem DaggerModels.OrdinaryRigidification.DaggerFreeComparison.canonicalFreeComparison_counit.{
  u
} :
  ∀ (C : DaggerModels.DaggerSimplicialCat.{u, u}),
    @Eq.{u + 1}
      (@Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
        (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.OrdinaryRigidification.coherentNerve.{u}
            (DaggerModels.DaggerSimplicialCat.toSimplicialCat.{u, u} C)))
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.id.{u, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
          C))
      (@CategoryTheory.CategoryStruct.comp.{u, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
        (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.OrdinaryRigidification.coherentNerve.{u}
            (DaggerModels.DaggerSimplicialCat.toSimplicialCat.{u, u} C)))
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.OrdinaryRigidification.coherentNerve.{u}
            (DaggerModels.DaggerSimplicialCat.toSimplicialCat.{u, u} C)))
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.id.{u, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
          C)
        (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Iso.hom.{u + 1, u + 1}
            (@CategoryTheory.Functor.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
            (@CategoryTheory.Functor.category.{u, u, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            canonicalFreeComparison.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.OrdinaryRigidification.coherentNerve.{u}
            (DaggerModels.DaggerSimplicialCat.toSimplicialCat.{u, u} C)))
        (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
              _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.forget.{u, u}
              DaggerModels.OrdinaryRigidification.coherentNerve.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u}))
          (@CategoryTheory.Functor.id.{u, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
          (@CategoryTheory.Adjunction.counit.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
              _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.forget.{u, u}
              DaggerModels.OrdinaryRigidification.coherentNerve.{u})
            canonicalTargetAdjunction.{u})
          C))
      (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u}))
        (@CategoryTheory.Functor.id.{u, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
        (@CategoryTheory.Adjunction.counit.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          sourceAdjunction.{u})
        C)
:=
  fun (C : DaggerModels.DaggerSimplicialCat.{u, u}) =>
    @freeComparison_counit.{u}
      DaggerModels.OrdinaryFreeDagger.functor.{u} DaggerModels.OrdinaryFreeDagger.adjunction.{u}
      C

theorem DaggerModels.OrdinaryRigidification.DaggerFreeComparison.canonicalFreeComparison_mate.{u} :
  ∀ (X : _root_.SSet.{u}),
    @Eq.{u + 1}
      (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
        (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
          (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u}))
        X
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            X)))
      (@DFunLike.coe.{u + 1, u + 1, u + 1}
        (Equiv.{u + 1, u + 1}
          (@Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
            (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
                DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
                DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
              X)
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                DaggerModels.SimplicialCat.instCategory.{u, u}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                DaggerModels.OrdinaryRigidification.rigidification.{u}
                DaggerModels.OrdinaryFreeDagger.functor.{u})
              X))
          (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
            (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
              (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u}))
            X
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
              SSet.largeCategory.{u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
                _root_.SSet.{u} SSet.largeCategory.{u}
                DaggerModels.DaggerSimplicialCat.forget.{u, u}
                DaggerModels.OrdinaryRigidification.coherentNerve.{u})
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.OrdinaryRigidification.rigidification.{u}
                  DaggerModels.OrdinaryFreeDagger.functor.{u})
                X))))
        (@Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
          (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            X)
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            X))
        (fun
            (_x :
              @Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
                (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
                    DaggerModels.DaggerSimplicialCat.{u, u}
                    DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
                (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                    SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
                    DaggerModels.DaggerSSet.instCategory.{u}
                    DaggerModels.DaggerSimplicialCat.{u, u}
                    DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                    DaggerModels.freeDagger.{u}
                  DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
                  X)
                (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                    SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                    DaggerModels.SimplicialCat.instCategory.{u, u}
                    DaggerModels.DaggerSimplicialCat.{u, u}
                    DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                    DaggerModels.OrdinaryRigidification.rigidification.{u}
                    DaggerModels.OrdinaryFreeDagger.functor.{u})
                  X)) =>
          @Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
            (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
              (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u}))
            X
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
              SSet.largeCategory.{u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
                _root_.SSet.{u} SSet.largeCategory.{u}
                DaggerModels.DaggerSimplicialCat.forget.{u, u}
                DaggerModels.OrdinaryRigidification.coherentNerve.{u})
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.OrdinaryRigidification.rigidification.{u}
                  DaggerModels.OrdinaryFreeDagger.functor.{u})
                X)))
        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1}
          (Equiv.{u + 1, u + 1}
            (@Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
              (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
                  DaggerModels.DaggerSSet.instCategory.{u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.freeDagger.{u}
                  DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
                X)
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.OrdinaryRigidification.rigidification.{u}
                  DaggerModels.OrdinaryFreeDagger.functor.{u})
                X))
            (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
              (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
                (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u}))
              X
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
                SSet.largeCategory.{u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.forget.{u, u}
                  DaggerModels.OrdinaryRigidification.coherentNerve.{u})
                (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                    SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                    DaggerModels.SimplicialCat.instCategory.{u, u}
                    DaggerModels.DaggerSimplicialCat.{u, u}
                    DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                    DaggerModels.OrdinaryRigidification.rigidification.{u}
                    DaggerModels.OrdinaryFreeDagger.functor.{u})
                  X))))
          (@Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
            (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
                DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
                DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
              X)
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                DaggerModels.SimplicialCat.instCategory.{u, u}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                DaggerModels.OrdinaryRigidification.rigidification.{u}
                DaggerModels.OrdinaryFreeDagger.functor.{u})
              X))
          (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
            (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
              (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u}))
            X
            (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
              SSet.largeCategory.{u}
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
                _root_.SSet.{u} SSet.largeCategory.{u}
                DaggerModels.DaggerSimplicialCat.forget.{u, u}
                DaggerModels.OrdinaryRigidification.coherentNerve.{u})
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.OrdinaryRigidification.rigidification.{u}
                  DaggerModels.OrdinaryFreeDagger.functor.{u})
                X)))
          (@Equiv.instEquivLike.{u + 1, u + 1}
            (@Quiver.Hom.{u + 1, u + 1} DaggerModels.DaggerSimplicialCat.{u, u}
              (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                (@CategoryTheory.Category.toCategoryStruct.{u, u + 1}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}))
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
                  DaggerModels.DaggerSSet.instCategory.{u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.freeDagger.{u}
                  DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
                X)
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.OrdinaryRigidification.rigidification.{u}
                  DaggerModels.OrdinaryFreeDagger.functor.{u})
                X))
            (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
              (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
                (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u}))
              X
              (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
                SSet.largeCategory.{u}
                (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
                  DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  DaggerModels.SimplicialCat.{u, u}
                  DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.forget.{u, u}
                  DaggerModels.OrdinaryRigidification.coherentNerve.{u})
                (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
                  SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                  DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                  (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                    SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                    DaggerModels.SimplicialCat.instCategory.{u, u}
                    DaggerModels.DaggerSimplicialCat.{u, u}
                    DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                    DaggerModels.OrdinaryRigidification.rigidification.{u}
                    DaggerModels.OrdinaryFreeDagger.functor.{u})
                  X)))))
        (@CategoryTheory.Adjunction.homEquiv.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          sourceAdjunction.{u} X
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            X))
        (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
            DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
            DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Iso.hom.{u + 1, u + 1}
            (@CategoryTheory.Functor.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
            (@CategoryTheory.Functor.category.{u, u, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            canonicalFreeComparison.{u})
          X))
      (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
        _root_.SSet.{u} SSet.largeCategory.{u}
        (@CategoryTheory.Functor.id.{u, u + 1} _root_.SSet.{u} SSet.largeCategory.{u})
        (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u}))
        (@CategoryTheory.Adjunction.unit.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          canonicalTargetAdjunction.{u})
        X)
:=
  fun (X : _root_.SSet.{u}) =>
    @freeComparison_mate.{u}
      DaggerModels.OrdinaryFreeDagger.functor.{u} DaggerModels.OrdinaryFreeDagger.adjunction.{u}
      X

theorem DaggerModels.OrdinaryRigidification.DaggerFreeComparison.canonicalFreeComparison_unit.{u} :
  ∀ (X : _root_.SSet.{u}),
    @Eq.{u + 1}
      (@Quiver.Hom.{u + 1, u + 1} _root_.SSet.{u}
        (@CategoryTheory.CategoryStruct.toQuiver.{u, u + 1} _root_.SSet.{u}
          (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u}))
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.Functor.id.{u, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}) X)
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            X)))
      (@CategoryTheory.CategoryStruct.comp.{u, u + 1} _root_.SSet.{u}
        (@CategoryTheory.Category.toCategoryStruct.{u, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u})
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.Functor.id.{u, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}) X)
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
          _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
              _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.forget.{u, u}
              DaggerModels.OrdinaryRigidification.coherentNerve.{u}))
          X)
        (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            X))
        (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} _root_.SSet.{u} SSet.largeCategory.{u}
          (@CategoryTheory.Functor.id.{u, u + 1} _root_.SSet.{u} SSet.largeCategory.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
            SSet.largeCategory.{u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
              _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.forget.{u, u}
              DaggerModels.OrdinaryRigidification.coherentNerve.{u}))
          (@CategoryTheory.Adjunction.unit.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
              _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.forget.{u, u}
              DaggerModels.OrdinaryRigidification.coherentNerve.{u})
            sourceAdjunction.{u})
          X)
        (@CategoryTheory.Functor.map.{u, u, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            X)
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            X)
          (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
              DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u}
              DaggerModels.OrdinaryFreeDagger.functor.{u})
            (@CategoryTheory.Iso.hom.{u + 1, u + 1}
              (@CategoryTheory.Functor.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
              (@CategoryTheory.Functor.category.{u, u, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u})
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
                DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
                DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
              (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
                SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
                DaggerModels.SimplicialCat.instCategory.{u, u}
                DaggerModels.DaggerSimplicialCat.{u, u}
                DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
                DaggerModels.OrdinaryRigidification.rigidification.{u}
                DaggerModels.OrdinaryFreeDagger.functor.{u})
              canonicalFreeComparison.{u})
            X)))
      (@CategoryTheory.NatTrans.app.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
        _root_.SSet.{u} SSet.largeCategory.{u}
        (@CategoryTheory.Functor.id.{u, u + 1} _root_.SSet.{u} SSet.largeCategory.{u})
        (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} _root_.SSet.{u}
          SSet.largeCategory.{u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u}))
        (@CategoryTheory.Adjunction.unit.{u, u, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
            DaggerModels.SimplicialCat.instCategory.{u, u}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.OrdinaryRigidification.rigidification.{u}
            DaggerModels.OrdinaryFreeDagger.functor.{u})
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          canonicalTargetAdjunction.{u})
        X)
:=
  fun (X : _root_.SSet.{u}) =>
    @freeComparison_unit.{u}
      DaggerModels.OrdinaryFreeDagger.functor.{u} DaggerModels.OrdinaryFreeDagger.adjunction.{u}
      X

theorem
  DaggerModels.OrdinaryRigidification.DaggerFreeComparison.lifted_adjunction_and_free_comparison.{
    u, u_1, u_2, u_3
  } :
  And
    (Nonempty.{u + 2}
      (@CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u}
        DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u}))
    (And
      (@Eq.{u_1 + 2}
        (@CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} DaggerModels.DaggerSSet.{u_1}
          DaggerModels.DaggerSSet.instCategory.{u_1} DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1})
        (@CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1}
          DaggerModels.DaggerSSet.{u_1} DaggerModels.DaggerSSet.instCategory.{u_1}
          DaggerModels.DaggerSimplicialCat.{u_1, u_1}
          DaggerModels.DaggerSimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_1}
          DaggerModels.DaggerSimplicialCat.forget.{u_1, u_1})
        (@CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1}
          DaggerModels.DaggerSSet.{u_1} DaggerModels.DaggerSSet.instCategory.{u_1}
          _root_.SSet.{u_1} SSet.largeCategory.{u_1} DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.DaggerSSet.forget.{u_1}
          DaggerModels.OrdinaryRigidification.rigidification.{u_1}))
      (And
        (@Eq.{u_2 + 2}
          (@CategoryTheory.Functor.{u_2, u_2, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.DaggerSSet.{u_2} DaggerModels.DaggerSSet.instCategory.{u_2}
            _root_.SSet.{u_2} SSet.largeCategory.{u_2}
            DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u_2}
            DaggerModels.DaggerSSet.forget.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.SimplicialCat.{u_2, u_2}
            DaggerModels.SimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2} DaggerModels.DaggerSimplicialCat.forget.{u_2, u_2}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u_2}))
        (Nonempty.{u_3 + 2}
          (@CategoryTheory.Iso.{u_3 + 1, u_3 + 1}
            (@CategoryTheory.Functor.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.category.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.DaggerSSet.{u_3}
              DaggerModels.DaggerSSet.instCategory.{u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.freeDagger.{u_3}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.SimplicialCat.{u_3, u_3}
              DaggerModels.SimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.OrdinaryRigidification.rigidification.{u_3}
              DaggerModels.OrdinaryFreeDagger.functor.{u_3})))))
:=
  @And.intro
    (Nonempty.{u + 2}
      (@CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u}
        DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u}))
    (And
      (@Eq.{u_1 + 2}
        (@CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} DaggerModels.DaggerSSet.{u_1}
          DaggerModels.DaggerSSet.instCategory.{u_1} DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1})
        (@CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1}
          DaggerModels.DaggerSSet.{u_1} DaggerModels.DaggerSSet.instCategory.{u_1}
          DaggerModels.DaggerSimplicialCat.{u_1, u_1}
          DaggerModels.DaggerSimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_1}
          DaggerModels.DaggerSimplicialCat.forget.{u_1, u_1})
        (@CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1}
          DaggerModels.DaggerSSet.{u_1} DaggerModels.DaggerSSet.instCategory.{u_1}
          _root_.SSet.{u_1} SSet.largeCategory.{u_1} DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.DaggerSSet.forget.{u_1}
          DaggerModels.OrdinaryRigidification.rigidification.{u_1}))
      (And
        (@Eq.{u_2 + 2}
          (@CategoryTheory.Functor.{u_2, u_2, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.DaggerSSet.{u_2} DaggerModels.DaggerSSet.instCategory.{u_2}
            _root_.SSet.{u_2} SSet.largeCategory.{u_2}
            DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u_2}
            DaggerModels.DaggerSSet.forget.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.SimplicialCat.{u_2, u_2}
            DaggerModels.SimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2} DaggerModels.DaggerSimplicialCat.forget.{u_2, u_2}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u_2}))
        (Nonempty.{u_3 + 2}
          (@CategoryTheory.Iso.{u_3 + 1, u_3 + 1}
            (@CategoryTheory.Functor.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.category.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.DaggerSSet.{u_3}
              DaggerModels.DaggerSSet.instCategory.{u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.freeDagger.{u_3}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.SimplicialCat.{u_3, u_3}
              DaggerModels.SimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.OrdinaryRigidification.rigidification.{u_3}
              DaggerModels.OrdinaryFreeDagger.functor.{u_3})))))
    (@Nonempty.intro.{u + 2}
      (@CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u}
        DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u})
      daggerRigidificationCoherentNerveAdjunction.{u})
    (@And.intro
      (@Eq.{u_1 + 2}
        (@CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} DaggerModels.DaggerSSet.{u_1}
          DaggerModels.DaggerSSet.instCategory.{u_1} DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1})
        (@CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1}
          DaggerModels.DaggerSSet.{u_1} DaggerModels.DaggerSSet.instCategory.{u_1}
          DaggerModels.DaggerSimplicialCat.{u_1, u_1}
          DaggerModels.DaggerSimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_1}
          DaggerModels.DaggerSimplicialCat.forget.{u_1, u_1})
        (@CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1}
          DaggerModels.DaggerSSet.{u_1} DaggerModels.DaggerSSet.instCategory.{u_1}
          _root_.SSet.{u_1} SSet.largeCategory.{u_1} DaggerModels.SimplicialCat.{u_1, u_1}
          DaggerModels.SimplicialCat.instCategory.{u_1, u_1}
          DaggerModels.DaggerSSet.forget.{u_1}
          DaggerModels.OrdinaryRigidification.rigidification.{u_1}))
      (And
        (@Eq.{u_2 + 2}
          (@CategoryTheory.Functor.{u_2, u_2, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.DaggerSSet.{u_2} DaggerModels.DaggerSSet.instCategory.{u_2}
            _root_.SSet.{u_2} SSet.largeCategory.{u_2}
            DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u_2}
            DaggerModels.DaggerSSet.forget.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.SimplicialCat.{u_2, u_2}
            DaggerModels.SimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2} DaggerModels.DaggerSimplicialCat.forget.{u_2, u_2}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u_2}))
        (Nonempty.{u_3 + 2}
          (@CategoryTheory.Iso.{u_3 + 1, u_3 + 1}
            (@CategoryTheory.Functor.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.category.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.DaggerSSet.{u_3}
              DaggerModels.DaggerSSet.instCategory.{u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.freeDagger.{u_3}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.SimplicialCat.{u_3, u_3}
              DaggerModels.SimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.OrdinaryRigidification.rigidification.{u_3}
              DaggerModels.OrdinaryFreeDagger.functor.{u_3}))))
      DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification_forget.{u_1}
      (@And.intro
        (@Eq.{u_2 + 2}
          (@CategoryTheory.Functor.{u_2, u_2, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.DaggerSSet.{u_2} DaggerModels.DaggerSSet.instCategory.{u_2}
            _root_.SSet.{u_2} SSet.largeCategory.{u_2}
            DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u_2}
            DaggerModels.DaggerSSet.forget.{u_2})
          (@CategoryTheory.Functor.comp.{u_2, u_2, u_2, u_2 + 1, u_2 + 1, u_2 + 1}
            DaggerModels.DaggerSimplicialCat.{u_2, u_2}
            DaggerModels.DaggerSimplicialCat.instCategory.{u_2, u_2}
            DaggerModels.SimplicialCat.{u_2, u_2}
            DaggerModels.SimplicialCat.instCategory.{u_2, u_2} _root_.SSet.{u_2}
            SSet.largeCategory.{u_2} DaggerModels.DaggerSimplicialCat.forget.{u_2, u_2}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u_2}))
        (Nonempty.{u_3 + 2}
          (@CategoryTheory.Iso.{u_3 + 1, u_3 + 1}
            (@CategoryTheory.Functor.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.category.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.DaggerSSet.{u_3}
              DaggerModels.DaggerSSet.instCategory.{u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.freeDagger.{u_3}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.SimplicialCat.{u_3, u_3}
              DaggerModels.SimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.OrdinaryRigidification.rigidification.{u_3}
              DaggerModels.OrdinaryFreeDagger.functor.{u_3})))
        DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve_forget.{u_2}
        (@Nonempty.intro.{u_3 + 2}
          (@CategoryTheory.Iso.{u_3 + 1, u_3 + 1}
            (@CategoryTheory.Functor.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.category.{u_3, u_3, u_3 + 1, u_3 + 1} _root_.SSet.{u_3}
              SSet.largeCategory.{u_3} DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.DaggerSSet.{u_3}
              DaggerModels.DaggerSSet.instCategory.{u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.freeDagger.{u_3}
              DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u_3})
            (@CategoryTheory.Functor.comp.{u_3, u_3, u_3, u_3 + 1, u_3 + 1, u_3 + 1}
              _root_.SSet.{u_3} SSet.largeCategory.{u_3} DaggerModels.SimplicialCat.{u_3, u_3}
              DaggerModels.SimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.{u_3, u_3}
              DaggerModels.DaggerSimplicialCat.instCategory.{u_3, u_3}
              DaggerModels.OrdinaryRigidification.rigidification.{u_3}
              DaggerModels.OrdinaryFreeDagger.functor.{u_3}))
          canonicalFreeComparison.{u_3})))

