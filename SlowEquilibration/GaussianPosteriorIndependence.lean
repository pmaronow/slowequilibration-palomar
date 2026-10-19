-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianUnaffectedRegression
public import SlowEquilibration.GaussianRegressionSchur

/-! Actual independence of Gaussian objects orthogonal to both the
conditioning observation and a second object, at every posterior target. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegressionCovariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
lemma standard_linear_independent_of_cross_zero (B : E →L[ℝ] G) (C : E →L[ℝ] H)
    (hBC : B.comp C.adjoint=0) : IndepFun B C (stdGaussian E) := by
  have hG:=(IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun (B.prod C)
  apply hG.indepFun_of_covariance_inner
  intro u v
  change cov[fun z:E=>inner ℝ u (B z),fun z:E=>inner ℝ v (C z);stdGaussian E]=0
  have hB : (fun z:E=>inner ℝ u (B z))=(fun z=>inner ℝ (B.adjoint u) z) := by
    funext z
    exact (B.adjoint_inner_left z u).symm
  have hC : (fun z:E=>inner ℝ v (C z))=(fun z=>inner ℝ (C.adjoint v) z) := by
    funext z
    exact (C.adjoint_inner_left z v).symm
  rw [hB,hC,← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian,innerSL_apply_apply,B.adjoint_inner_left]
  have hz:=congrArg (fun T:H→L[ℝ]G=>T v) hBC
  change B (C.adjoint v)=0 at hz
  rw [hz,inner_zero_right]

/-- Genuine posterior independence under the actual affine Gaussian
regression kernel; the second object's conditional covariance may be singular. -/
theorem regression_linear_independent_of_cross_zero (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) (C : E →L[ℝ] H) (hBA : B.comp A.adjoint=0)
    (hBC : B.comp C.adjoint=0) (w : F) : IndepFun B C (regressionKernel A w) := by
  have hBres:=residual_map_eq_of_cross_zero A B hBA
  have hcross : B.comp (C.comp (residual A)).adjoint=0 := by
    rw [ContinuousLinearMap.adjoint_comp,residual_adjoint A hA,← ContinuousLinearMap.comp_assoc,hBres,hBC]
  have hi : IndepFun (B:E→G) (fun z:E=>C (residual A z)+C (lift A w)) (stdGaussian E) := by
    simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_apply] using
      (standard_linear_independent_of_cross_zero B (C.comp (residual A)) hcross).comp
        (φ:=id) (ψ:=fun z:H=>z+C (lift A w)) measurable_id (measurable_id.add measurable_const)
  let T : E → E:=fun z=>residual A z+lift A w
  have hT : Measurable T:=(residual A).continuous.measurable.add measurable_const
  have hBT (z : E) : B (T z)=B z := by
    change B (residual A z+lift A w)=B z
    rw [map_add,lift_map_eq_zero_of_cross_zero A B hBA,add_zero]
    exact congrArg (fun L:E→L[ℝ]G=>L z) hBres
  have hCT (z : E) : C (T z)=C (residual A z)+C (lift A w) := C.map_add _ _
  rw [regressionKernel_apply]
  change IndepFun B C ((stdGaussian E).map T)
  rw [indepFun_iff_map_prod_eq_prod_map_map B.continuous.measurable.aemeasurable C.continuous.measurable.aemeasurable]
  rw [Measure.map_map (B.continuous.measurable.prodMk C.continuous.measurable) hT,
    Measure.map_map B.continuous.measurable hT,Measure.map_map C.continuous.measurable hT]
  have hepair : (fun z:E=>(B z,C z)) ∘ T=(fun z:E=>(B z,C (residual A z)+C (lift A w))) := by
    funext z
    exact Prod.ext (hBT z) (hCT z)
  have heB : B ∘ T=(B:E→G) := by funext z;exact hBT z
  have heC : C ∘ T=(fun z:E=>C (residual A z)+C (lift A w)) := by funext z;exact hCT z
  rw [hepair,heB,heC]
  exact hi.map_prod_eq_prod_map_map B.continuous.measurable.aemeasurable
    ((C.comp (residual A)).continuous.measurable.add measurable_const).aemeasurable

end
end SlowEquilibration.GaussianRegressionCovariance

namespace SlowEquilibration.SphericalConditionalMatrices
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance
variable {N P : ℕ} {F G H : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The same independence holds for actual objects of the complete original
tensor field, under its actual canonical full-disorder posterior. -/
theorem coefficientKernel_independent_of_cross_zero
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A)
    (B : EuclideanDisorder N P →L[ℝ] G) (C : EuclideanDisorder N P →L[ℝ] H)
    (hBA : B.comp A.adjoint=0) (hBC : B.comp C.adjoint=0) (w : F) :
    IndepFun (actualObservation B) (actualObservation C) (coefficientKernel A w) := by
  have hi:=regression_linear_independent_of_cross_zero A hA B C hBA hBC w
  have hmB : Measurable (actualObservation B) :=
    B.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P=>ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable N P))
  have hmC : Measurable (actualObservation C) :=
    C.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P=>ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable N P))
  rw [indepFun_iff_map_prod_eq_prod_map_map hmB.aemeasurable hmC.aemeasurable,coefficientKernel_apply]
  rw [Measure.map_map (hmB.prodMk hmC) (unpackCLM N P).continuous.measurable,
    Measure.map_map hmB (unpackCLM N P).continuous.measurable,
    Measure.map_map hmC (unpackCLM N P).continuous.measurable]
  exact hi.map_prod_eq_prod_map_map B.continuous.measurable.aemeasurable C.continuous.measurable.aemeasurable

end
end SlowEquilibration.SphericalConditionalMatrices
