-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegression
public import SlowEquilibration.GaussianMatrixMomentLaw

/-! Actual canonical Gaussian conditioning decreases every scalar linear
variance. The centered conditional law is constructed from the full Gaussian
coefficient residual, including singular conditional covariance. -/

@[expose] public section
namespace SlowEquilibration.GaussianRegressionCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open GaussianRegression
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- The genuine centered conditional law of a coefficient-linear object. -/
def centeredLaw (A : E →L[ℝ] F) (B : E →L[ℝ] G) : Measure G :=
  (stdGaussian E).map (B.comp (residual A))

def conditionalLaw (A : E →L[ℝ] F) (B : E →L[ℝ] G) (w : F) : Measure G :=
  (regressionKernel A w).map B

instance centeredLaw_probability (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    IsProbabilityMeasure (centeredLaw A B) := by unfold centeredLaw;infer_instance

instance centeredLaw_gaussian (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    IsGaussian (centeredLaw A B) :=
  ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun (B.comp (residual A))).isGaussian_map

omit [MeasurableSpace F] [BorelSpace F] in
lemma centeredLaw_mean (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    ∫ z,z ∂centeredLaw A B = 0 := by
  rw [centeredLaw,integral_map (φ := B.comp (residual A)) (f := fun z : G => z)
    (B.comp (residual A)).continuous.measurable.aemeasurable aestronglyMeasurable_id]
  rw [(B.comp (residual A)).integral_comp_id_comm IsGaussian.integrable_id,integral_id_stdGaussian,map_zero]

omit [FiniteDimensional ℝ G] in
/-- At every specified null target, the actual conditional law is a fixed
Gaussian residual translated by its true regression mean. -/
lemma conditionalLaw_eq_translate (A : E →L[ℝ] F) (B : E →L[ℝ] G) (w : F) :
    conditionalLaw A B w=(centeredLaw A B).map (fun z => z+B (lift A w)) := by
  rw [conditionalLaw,regressionKernel_apply,centeredLaw,
    Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact B.map_add _ _

lemma conditionalLaw_mean (A : E →L[ℝ] F) (B : E →L[ℝ] G) (w : F) :
    ∫ z,z ∂conditionalLaw A B w=B (lift A w) := by
  rw [conditionalLaw_eq_translate,integral_map (φ := fun z : G => z+B (lift A w)) (f := fun z : G => z)
    (by fun_prop) aestronglyMeasurable_id,
    integral_add IsGaussian.integrable_fun_id (integrable_const _),centeredLaw_mean]
  simp

omit [FiniteDimensional ℝ G] in
/-- Actual canonical centering gives the fixed residual law for every target. -/
lemma conditionalLaw_centered (A : E →L[ℝ] F) (B : E →L[ℝ] G) (w : F) :
    (conditionalLaw A B w).map (fun z => z-B (lift A w))=centeredLaw A B := by
  rw [conditionalLaw_eq_translate,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun z : G => z-B (lift A w)) ∘ (fun z => z+B (lift A w)))=id := by
    funext z
    simp
  rw [he,Measure.map_id]

omit [MeasurableSpace F] [BorelSpace F] in
/-- The orthogonal regression residual cannot increase any true scalar
linear variance of the original standard Gaussian coefficients. -/
lemma residual_linear_variance_le (A : E →L[ℝ] F) (hA : Surjective A) (f : E →L[ℝ] ℝ) :
    Var[fun x => f (residual A x);stdGaussian E] ≤ Var[f;stdGaussian E] := by
  change Var[f.comp (residual A);stdGaussian E] ≤ _
  rw [variance_dual_stdGaussian,variance_dual_stdGaussian]
  have hR : ‖residual A‖ ≤ 1 := by
    rw [residual_eq_starProjection A hA]
    exact A.ker.starProjection_norm_le
  have hnorm : ‖f.comp (residual A)‖ ≤ ‖f‖ :=
    (f.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg f) hR)
  nlinarith [norm_nonneg (f.comp (residual A)),norm_nonneg f]

omit [FiniteDimensional ℝ G] [MeasurableSpace F] [BorelSpace F] in
/-- Genuine conditional covariance domination for every scalar observation;
this is proved from the actual coefficient residual projection. -/
theorem centeredLaw_variance_le (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) (f : G →L[ℝ] ℝ) :
    Var[f;centeredLaw A B] ≤ Var[f;(stdGaussian E).map B] := by
  rw [centeredLaw,variance_map f.continuous.measurable.aemeasurable (by fun_prop),
    variance_map f.continuous.measurable.aemeasurable B.continuous.measurable.aemeasurable]
  exact residual_linear_variance_le A hA (f.comp B)

omit [MeasurableSpace F] [BorelSpace F] in
/-- The literal symmetric-test trace covariance bound is preserved by actual
conditioning of any genuine coefficient-linear symmetric matrix. -/
theorem centered_matrix_trace_variance_le {m : ℕ}
    (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] GOEAsymptotics.GaussianMatrix m)
    (M : GOEAsymptotics.GaussianMatrix m) (hM : ∀ i j,M i j=M j i) :
    Var[fun W => Matrix.trace (SymmetricGaussianCovariance.entries W*
      SymmetricGaussianCovariance.entries M);centeredLaw A B] ≤
    Var[fun W => Matrix.trace (SymmetricGaussianCovariance.entries W*
      SymmetricGaussianCovariance.entries M);(stdGaussian E).map B] := by
  simp_rw [SymmetricGaussianCovariance.trace_mul_eq_inner _ M hM]
  exact centeredLaw_variance_le A hA B (innerSL ℝ M)

end
end SlowEquilibration.GaussianRegressionCovariance
