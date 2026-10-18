import DaggerModels.DaggerAdjunction
import DaggerModels.FreeDagger
import Mathlib.CategoryTheory.Adjunction.Unique

/-! Original free comparison, recovered with its unchanged typed construction and proof terms. -/

set_option autoImplicit false
set_option maxRecDepth 100000
open DaggerModels.OrdinaryRigidification.DaggerAdjunction

noncomputable def DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u} :
  @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
    DaggerModels.DaggerSimplicialCat.{u, u} DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
    (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
      SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
      DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
      DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
    (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
      DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
      DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.forget.{u, u}
      DaggerModels.OrdinaryRigidification.coherentNerve.{u})
:=
  @CategoryTheory.Adjunction.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
    SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u} DaggerModels.DaggerSSet.instCategory.{u}
    DaggerModels.freeDagger.{u} DaggerModels.DaggerSSet.forget.{u}
    DaggerModels.DaggerSimplicialCat.{u, u} DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
    DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u}
    DaggerModels.OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{u}
    DaggerModels.freeDaggerAdjunction.{u}
    daggerRigidificationCoherentNerveAdjunction.{u}

noncomputable def DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} :
  {L :
      @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}} →
    @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
        DaggerModels.DaggerSimplicialCat.forget.{u, u} →
      @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} _root_.SSet.{u} SSet.largeCategory.{u}
        DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
          SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
          DaggerModels.OrdinaryRigidification.rigidification.{u} L)
        (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
          DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
          DaggerModels.DaggerSimplicialCat.forget.{u, u}
          DaggerModels.OrdinaryRigidification.coherentNerve.{u})
:=
  fun
      {L :
        @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
      (freeAdjunction :
        @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
          DaggerModels.DaggerSimplicialCat.forget.{u, u}) =>
    @CategoryTheory.Adjunction.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
      SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
      DaggerModels.SimplicialCat.instCategory.{u, u}
      DaggerModels.OrdinaryRigidification.rigidification.{u}
      DaggerModels.OrdinaryRigidification.coherentNerve.{u}
      DaggerModels.DaggerSimplicialCat.{u, u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
      DaggerModels.DaggerSimplicialCat.forget.{u, u}
      DaggerModels.OrdinaryRigidification.rigidificationCoherentNerveAdjunction.{u}
      freeAdjunction

noncomputable def DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison.{u} :
  {L :
      @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}} →
    @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
        DaggerModels.DaggerSimplicialCat.forget.{u, u} →
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
          DaggerModels.OrdinaryRigidification.rigidification.{u} L)
:=
  fun
      {L :
        @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
      (freeAdjunction :
        @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
          DaggerModels.DaggerSimplicialCat.forget.{u, u}) =>
    @CategoryTheory.Adjunction.leftAdjointUniq.{u, u + 1, u, u + 1} _root_.SSet.{u}
      DaggerModels.DaggerSimplicialCat.{u, u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.rigidification.{u} L)
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
        DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
        DaggerModels.DaggerSimplicialCat.forget.{u, u}
        DaggerModels.OrdinaryRigidification.coherentNerve.{u})
      DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u}
      (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
        freeAdjunction)

theorem DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison_counit.{u} :
  ∀
    {L :
      @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
    (freeAdjunction :
      @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
        DaggerModels.DaggerSimplicialCat.forget.{u, u})
    (C : DaggerModels.DaggerSimplicialCat.{u, u}),
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
            (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison.{u} L
              freeAdjunction))
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L))
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
              _root_.SSet.{u} SSet.largeCategory.{u}
              DaggerModels.DaggerSimplicialCat.forget.{u, u}
              DaggerModels.OrdinaryRigidification.coherentNerve.{u})
            (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
              freeAdjunction))
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
          DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u})
        C)
:=
  fun
      {L :
        @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
      (freeAdjunction :
        @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
          DaggerModels.DaggerSimplicialCat.forget.{u, u})
      (C : DaggerModels.DaggerSimplicialCat.{u, u}) =>
    @CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit.{u, u + 1, u, u + 1}
      _root_.SSet.{u} DaggerModels.DaggerSimplicialCat.{u, u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.rigidification.{u} L)
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
        DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
        DaggerModels.DaggerSimplicialCat.forget.{u, u}
        DaggerModels.OrdinaryRigidification.coherentNerve.{u})
      DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u}
      (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
        freeAdjunction)
      C

theorem DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison_mate.{u} :
  ∀
    {L :
      @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
    (freeAdjunction :
      @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
        DaggerModels.DaggerSimplicialCat.forget.{u, u})
    (X : _root_.SSet.{u}),
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                  DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                    DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                  DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                  DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                    DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                  DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                  DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                    DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
          DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u} X
          (@CategoryTheory.Functor.obj.{u, u, u + 1, u + 1} _root_.SSet.{u}
            SSet.largeCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
              SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
              DaggerModels.SimplicialCat.instCategory.{u, u}
              DaggerModels.DaggerSimplicialCat.{u, u}
              DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
            (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison.{u} L
              freeAdjunction))
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
            freeAdjunction))
        X)
:=
  fun
      {L :
        @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
      (freeAdjunction :
        @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
          DaggerModels.DaggerSimplicialCat.forget.{u, u})
      (X : _root_.SSet.{u}) =>
    @CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app.{u, u + 1, u, u + 1}
      _root_.SSet.{u} DaggerModels.DaggerSimplicialCat.{u, u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.rigidification.{u} L)
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
        DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
        DaggerModels.DaggerSimplicialCat.forget.{u, u}
        DaggerModels.OrdinaryRigidification.coherentNerve.{u})
      DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u}
      (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
        freeAdjunction)
      X

theorem DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison_unit.{u} :
  ∀
    {L :
      @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
    (freeAdjunction :
      @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
        DaggerModels.DaggerSimplicialCat.forget.{u, u})
    (X : _root_.SSet.{u}),
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
            DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u})
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
              DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
                DaggerModels.OrdinaryRigidification.rigidification.{u} L)
              (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.freeComparison.{u} L
                freeAdjunction))
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
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
            DaggerModels.OrdinaryRigidification.rigidification.{u} L)
          (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
            DaggerModels.DaggerSimplicialCat.{u, u}
            DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
            DaggerModels.SimplicialCat.{u, u} DaggerModels.SimplicialCat.instCategory.{u, u}
            _root_.SSet.{u} SSet.largeCategory.{u}
            DaggerModels.DaggerSimplicialCat.forget.{u, u}
            DaggerModels.OrdinaryRigidification.coherentNerve.{u})
          (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
            freeAdjunction))
        X)
:=
  fun
      {L :
        @CategoryTheory.Functor.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u}}
      (freeAdjunction :
        @CategoryTheory.Adjunction.{u, u, u + 1, u + 1} DaggerModels.SimplicialCat.{u, u}
          DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
          DaggerModels.DaggerSimplicialCat.instCategory.{u, u} L
          DaggerModels.DaggerSimplicialCat.forget.{u, u})
      (X : _root_.SSet.{u}) =>
    @CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app.{u, u + 1, u, u + 1} _root_.SSet.{u}
      DaggerModels.DaggerSimplicialCat.{u, u} SSet.largeCategory.{u}
      DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.DaggerSSet.{u}
        DaggerModels.DaggerSSet.instCategory.{u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.freeDagger.{u}
        DaggerModels.OrdinaryRigidification.DaggerRigidification.daggerRigidification.{u})
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1} _root_.SSet.{u}
        SSet.largeCategory.{u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u}
        DaggerModels.OrdinaryRigidification.rigidification.{u} L)
      (@CategoryTheory.Functor.comp.{u, u, u, u + 1, u + 1, u + 1}
        DaggerModels.DaggerSimplicialCat.{u, u}
        DaggerModels.DaggerSimplicialCat.instCategory.{u, u} DaggerModels.SimplicialCat.{u, u}
        DaggerModels.SimplicialCat.instCategory.{u, u} _root_.SSet.{u} SSet.largeCategory.{u}
        DaggerModels.DaggerSimplicialCat.forget.{u, u}
        DaggerModels.OrdinaryRigidification.coherentNerve.{u})
      DaggerModels.OrdinaryRigidification.DaggerFreeComparison.sourceAdjunction.{u}
      (@DaggerModels.OrdinaryRigidification.DaggerFreeComparison.targetAdjunction.{u} L
        freeAdjunction)
      X

