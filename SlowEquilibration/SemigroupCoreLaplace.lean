-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemigroupLaplaceShift
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Identification of the actual Laplace integral from a genuine differential core. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SemigroupLaplace.Data
open Set MeasureTheory Filter
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : SlowEquilibration.SemigroupLaplace.Data E)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem P_operator_hasDerivWithinAt_zero (x : E) :
    HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal (S.operator x))
      (S.operator x-x) (Ici 0) 0 := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    ((S.integrand_continuous x).intervalIntegrable 0 0)
    (S.integrand_continuous x).stronglyMeasurable.stronglyMeasurableAtFilter
    (S.integrand_continuous x).continuousAt
  have hd := (Real.hasDerivAt_exp 0).smul ((hasDerivAt_const 0 (S.operator x)).sub hi)
  have hd' : HasDerivAt
      (fun r : ℝ => Real.exp r • (S.operator x-∫ u : ℝ in (0 : ℝ)..r,S.integrand x u))
      (S.operator x-x) 0 := by
    convert hd using 1
    simp only [integrand,Real.toNNReal_zero,S.zero,ContinuousLinearMap.id_apply,
      neg_zero,Real.exp_zero,one_smul,zero_sub,Pi.sub_apply,intervalIntegral.integral_same,sub_zero]
    abel
  apply hd'.hasDerivWithinAt.congr_of_mem
  · intro r hr
    have he := S.P_operator_shift r.toNNReal x
    simpa only [Real.coe_toNNReal r hr] using he
  · exact self_mem_Ici

theorem operator_of_derivative_zero (x v : E)
    (hd : HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal x) v (Ici 0) 0) :
    S.operator v=S.operator x-x := by
  have hQ := S.operator.hasFDerivAt.comp_hasDerivWithinAt 0 hd
  have hh : HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal (S.operator x))
      (S.operator v) (Ici 0) 0 := by
    simpa only [Function.comp_def,S.operator_commutes] using hQ
  exact UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffWithinAt_Ici 0) hh
    (S.P_operator_hasDerivWithinAt_zero x)

/-- A right generator derivative on a proved graph core determines the
Laplace integral on the whole closed operator domain. -/
theorem operator_add_generator (A : E →ₗ.[ℝ] E) (hA : A.IsClosed)
    (C : Submodule ℝ E) (hC : A.HasCore C)
    (hd : ∀ x : C,HasDerivWithinAt (fun r : ℝ => S.P r.toNNReal x)
      (-A ⟨x,hC.le_domain x.property⟩) (Ici 0) 0) (x : A.domain) :
    S.operator ((x : E)+A x)=x := by
  let F : Set (E×E) := {z | S.operator (z.1+z.2)=z.1}
  have hF : IsClosed F := isClosed_eq
    (S.operator.continuous.comp (continuous_fst.add continuous_snd)) continuous_fst
  have hsub : ((A.domRestrict C).graph : Set (E×E))⊆F := by
    intro z hz
    obtain ⟨y,hy,hAy⟩ := (A.domRestrict C).mem_graph_iff.mp hz
    have he := S.operator_of_derivative_zero (y : E) (-A ⟨y,hC.le_domain y.property.1⟩)
      (hd ⟨y,y.property.1⟩)
    have he' : S.operator ((y : E)+A ⟨y,hC.le_domain y.property.1⟩)=y := by
      rw [map_neg] at he
      rw [map_add]
      have hh := congrArg (fun z : E => z+(y : E)+S.operator (A ⟨y,hC.le_domain y.property.1⟩)) he
      convert hh.symm using 1 <;> abel
    change S.operator (z.1+z.2)=z.1
    rw [← hy,← hAy]
    exact he'
  have hclosable := hA.isClosable.leIsClosable (show A.domRestrict C ≤ A from LinearPMap.domRestrict_le)
  have heq : (A.domRestrict C).graph.topologicalClosure=A.graph := by
    rw [hclosable.graph_closure_eq_closure_graph,hC.closure_eq]
  have hs := closure_minimal hsub hF
  have hx : ((x : E),A x)∈closure ((A.domRestrict C).graph : Set (E×E)) := by
    change ((x : E),A x)∈(A.domRestrict C).graph.topologicalClosure
    rw [heq]
    exact A.mem_graph x
  exact hs hx

end SlowEquilibration.SemigroupLaplace.Data
