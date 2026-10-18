import DaggerModels.FreeDaggerSimplicialCategory
import DaggerModels.DaggerHomKernel
import DaggerModels.DaggerHomQuotient
import Mathlib.CategoryTheory.Adjunction.Basic
import OriginalRecoveredKernelExpression

/-! Original free dagger construction, recovered as explicit shared kernel terms.

All 45 original declarations retain their names, universe parameters, types, and bodies.
The supporting data contains ordinary expression syntax, not compiled theorem imports.
The normal Lean kernel rechecks every declaration against the current native dependencies.
A separate fidelity probe compares their types and values with the original preserved module.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

abbrev DaggerModels.OrdinaryFreeDagger.Model.{u} :
  recovered_kernel_expr% 1756 :=
  recovered_kernel_expr% 1763

theorem DaggerModels.OrdinaryFreeDagger.doubledHom._proof_1.{u_1} :
  recovered_kernel_expr% 609 :=
  recovered_kernel_expr% 820

theorem DaggerModels.OrdinaryFreeDagger.doubledHom._proof_2.{u_1} :
  recovered_kernel_expr% 163 :=
  recovered_kernel_expr% 551

noncomputable def DaggerModels.OrdinaryFreeDagger.doubledHom.{u} :
  recovered_kernel_expr% 2656 :=
  recovered_kernel_expr% 2724

theorem DaggerModels.OrdinaryFreeDagger.doubledDagger._proof_1.{u_1} :
  recovered_kernel_expr% 5806 :=
  recovered_kernel_expr% 5952

noncomputable def DaggerModels.OrdinaryFreeDagger.doubledDagger.{u} :
  recovered_kernel_expr% 1720 :=
  recovered_kernel_expr% 1754

theorem DaggerModels.OrdinaryFreeDagger.graph._proof_1.{u_1} :
  recovered_kernel_expr% 2822 :=
  recovered_kernel_expr% 2972

noncomputable def DaggerModels.OrdinaryFreeDagger.graph.{u} :
  recovered_kernel_expr% 2529 :=
  recovered_kernel_expr% 2540

theorem DaggerModels.OrdinaryFreeDagger.assignment._proof_1.{u_1} :
  recovered_kernel_expr% 2132 :=
  recovered_kernel_expr% 2519

theorem DaggerModels.OrdinaryFreeDagger.assignment._proof_2.{u_1} :
  recovered_kernel_expr% 3056 :=
  recovered_kernel_expr% 3303

noncomputable def DaggerModels.OrdinaryFreeDagger.free.{u} :
  recovered_kernel_expr% 2541 :=
  recovered_kernel_expr% 2552

theorem DaggerModels.OrdinaryFreeDagger.positive._proof_1.{u_1} :
  recovered_kernel_expr% 8258 :=
  recovered_kernel_expr% 8268

theorem DaggerModels.OrdinaryFreeDagger.assignment._proof_3.{u_1} :
  recovered_kernel_expr% 3471 :=
  recovered_kernel_expr% 5760

noncomputable def DaggerModels.OrdinaryFreeDagger.positive.{u} :
  recovered_kernel_expr% 8272 :=
  recovered_kernel_expr% 8287

noncomputable def DaggerModels.OrdinaryFreeDagger.assignment.{u} :
  recovered_kernel_expr% 8667 :=
  recovered_kernel_expr% 8748

noncomputable def DaggerModels.OrdinaryFreeDagger.edge.{u} :
  recovered_kernel_expr% 7179 :=
  recovered_kernel_expr% 7210

noncomputable def DaggerModels.OrdinaryFreeDagger.evaluator.{u} :
  recovered_kernel_expr% 8751 :=
  recovered_kernel_expr% 8761

theorem DaggerModels.OrdinaryFreeDagger.edge_evaluator.{u} :
  recovered_kernel_expr% 7267 :=
  recovered_kernel_expr% 7467

noncomputable def DaggerModels.OrdinaryFreeDagger.rel.{u} :
  recovered_kernel_expr% 7500 :=
  recovered_kernel_expr% 7532

theorem DaggerModels.OrdinaryFreeDagger.edge_evaluator_app.{u} :
  recovered_kernel_expr% 1874 :=
  recovered_kernel_expr% 1928

theorem DaggerModels.OrdinaryFreeDagger.relation._proof_1.{u_1} :
  recovered_kernel_expr% 8145 :=
  recovered_kernel_expr% 8167

theorem DaggerModels.OrdinaryFreeDagger.relation._proof_2.{u_1} :
  recovered_kernel_expr% 2635 :=
  recovered_kernel_expr% 2653

theorem DaggerModels.OrdinaryFreeDagger.rel_comp.{u} :
  recovered_kernel_expr% 1063 :=
  recovered_kernel_expr% 1688

theorem DaggerModels.OrdinaryFreeDagger.rel_id.{u} :
  recovered_kernel_expr% 7814 :=
  recovered_kernel_expr% 8074

noncomputable def DaggerModels.OrdinaryFreeDagger.relation.{u} :
  recovered_kernel_expr% 826 :=
  recovered_kernel_expr% 838

noncomputable def DaggerModels.OrdinaryFreeDagger.category.{u} :
  recovered_kernel_expr% 2541 :=
  recovered_kernel_expr% 8292

theorem DaggerModels.OrdinaryFreeDagger.kills.{u} :
  recovered_kernel_expr% 8622 :=
  recovered_kernel_expr% 8655

noncomputable def DaggerModels.OrdinaryFreeDagger.lift.{u} :
  recovered_kernel_expr% 2977 :=
  recovered_kernel_expr% 2986

noncomputable def DaggerModels.OrdinaryFreeDagger.quotient.{u} :
  recovered_kernel_expr% 8295 :=
  recovered_kernel_expr% 8299

theorem DaggerModels.OrdinaryFreeDagger.quotient_lift.{u} :
  recovered_kernel_expr% 1788 :=
  recovered_kernel_expr% 1803

theorem DaggerModels.OrdinaryFreeDagger.unit._proof_1.{u_1} :
  recovered_kernel_expr% 6907 :=
  recovered_kernel_expr% 7145

theorem DaggerModels.OrdinaryFreeDagger.unit._proof_2.{u_1} :
  recovered_kernel_expr% 6076 :=
  recovered_kernel_expr% 6840

noncomputable def DaggerModels.OrdinaryFreeDagger.unit.{u} :
  recovered_kernel_expr% 8171 :=
  recovered_kernel_expr% 8222

noncomputable def DaggerModels.OrdinaryFreeDagger.restrict.{u} :
  recovered_kernel_expr% 873 :=
  recovered_kernel_expr% 897

theorem DaggerModels.OrdinaryFreeDagger.unit_map_app.{u} :
  recovered_kernel_expr% 2782 :=
  recovered_kernel_expr% 2790

theorem DaggerModels.OrdinaryFreeDagger.unit_obj.{u} :
  recovered_kernel_expr% 7161 :=
  recovered_kernel_expr% 7165

theorem DaggerModels.OrdinaryFreeDagger.lift_restrict.{u} :
  recovered_kernel_expr% 8769 :=
  recovered_kernel_expr% 9295

theorem DaggerModels.OrdinaryFreeDagger.restrict_lift.{u} :
  recovered_kernel_expr% 7542 :=
  recovered_kernel_expr% 7739

noncomputable def DaggerModels.OrdinaryFreeDagger.homEquiv.{u} :
  recovered_kernel_expr% 7744 :=
  recovered_kernel_expr% 7763

theorem DaggerModels.OrdinaryFreeDagger.homEquiv_naturality.{u} :
  recovered_kernel_expr% 8368 :=
  recovered_kernel_expr% 8499

noncomputable def DaggerModels.OrdinaryFreeDagger.functor.{u} :
  recovered_kernel_expr% 1693 :=
  recovered_kernel_expr% 1704

noncomputable def DaggerModels.OrdinaryFreeDagger.adjunction.{u} :
  recovered_kernel_expr% 7474 :=
  recovered_kernel_expr% 7483

theorem DaggerModels.OrdinaryFreeDagger.functor_obj.{u} :
  recovered_kernel_expr% 2524 :=
  recovered_kernel_expr% 2527

theorem DaggerModels.OrdinaryFreeDagger.functor_obj_Obj.{u} :
  recovered_kernel_expr% 1941 :=
  recovered_kernel_expr% 1945

theorem DaggerModels.OrdinaryFreeDagger.adjunction_unit.{u} :
  recovered_kernel_expr% 8542 :=
  recovered_kernel_expr% 8614

