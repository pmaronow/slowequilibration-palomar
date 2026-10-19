-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairProjectedJetConcentration
public import SlowEquilibration.SourcePhysicalPairPosteriorMeanBounds

/-! Actual posterior tensor-jet tails. The original coefficient kernel is
represented by its orthogonal Gaussian residual and its canonical lift;
the tensor block contraction and mean shift are proved directly. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalAging.FiniteModel WholeFieldRegression GaussianRegression
open PureTensorJetFeatures PureTensorJetBounds PureTensorJetConcentration
open NormalizedPairObservations PairObservationTargets NormalizedObservationCoercivity
open GaussianObservationCoercivity
open scoped ENNReal BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sourceDegreeProjectionCLM {N P:ℕ} (p:Degree P) :
    EuclideanDisorder N P→L[ℝ]EuclideanSpace ℝ (TensorIndex N p.val.val):=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _:TensorIndex N p.val.val=>ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun I=>EuclideanSpace.proj ⟨p,I⟩))

lemma sourceDegreeProjectionCLM_norm_le {N P:ℕ} (p:Degree P) :
    ‖sourceDegreeProjectionCLM (N:=N) p‖ ≤ 1:=by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro g
  have hs:=projection_norm_sum (N:=N) (fun q:Degree P=>q.val.val) g
  have hb:‖blockProjection (fun q:Degree P=>q.val.val) p g‖^2 ≤ ‖g‖^2:=by
    rw [←hs]
    exact Finset.single_le_sum (fun q _=>sq_nonneg (‖blockProjection (fun q:Degree P=>q.val.val) q g‖)) (Finset.mem_univ p)
  change ‖blockProjection (fun q:Degree P=>q.val.val) p g‖ ≤ 1*‖g‖
  simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hb

@[simp] lemma sourceDegreeProjectionCLM_unpack {N P:ℕ} (p:Degree P)
    (g:EuclideanDisorder N P) :
    WithLp.ofLp (sourceDegreeProjectionCLM p g)=(unpackCLM N P g) p:=rfl

lemma sourceCoefficientKernel_affine {N P:ℕ} {F:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A:EuclideanDisorder N P→L[ℝ]F) (w:F) :
    coefficientKernel A w=(SYK.standardGaussianMeasureOnEuclidean (SphericalModel.Coordinate N P)).map
      (fun g=>unpackCLM N P (residual A g+lift A w)):=by
  rw [coefficientKernel_apply,regressionKernel_apply,Measure.map_map
    (unpackCLM N P).continuous.measurable (by fun_prop)]
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian,Function.comp_def]

theorem source_posterior_unitJet_tail {N P j:ℕ} {F:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (hN:0<N) (A:EuclideanDisorder N P→L[ℝ]F) (hA:Surjective A)
    (w:F) {K:ℝ} (hm:‖lift A w‖ ≤ K*Real.sqrt N) (p:Degree P) :
    (coefficientKernel A w).real
      {J|(2*((j:ℝ)+2)*(p.val.val:ℝ)^j*Real.sqrt p.val.val+1+(p.val.val:ℝ)^j*K)*Real.sqrt N ≤
        unitJetEnvelope N p.val.val j (J p)} ≤
      Real.exp (-(N:ℝ)/(2*((p.val.val:ℝ)^j)^2)):=by
  let T:EuclideanDisorder N P→L[ℝ]EuclideanSpace ℝ (TensorIndex N p.val.val):=
    (sourceDegreeProjectionCLM p).comp (residual A)
  have hr:‖residual A‖ ≤ 1:=by rw [residual_eq_starProjection A hA];exact A.ker.starProjection_norm_le
  have hT:‖T‖ ≤ 1:=by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [sourceDegreeProjectionCLM_norm_le (N:=N) p,norm_nonneg (sourceDegreeProjectionCLM (N:=N) p)])
  let m:=sourceDegreeProjectionCLM p (lift A w)
  have hshift:‖m‖ ≤ K*Real.sqrt N:=by
    exact ((sourceDegreeProjectionCLM p).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (sourceDegreeProjectionCLM_norm_le p) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hm))
  have hp:1 ≤ p.val.val:=by have :=p.property;omega
  have ht:=sourceProjectedAffineUnitJetEnvelope_tail (j:=j) hN hp T hT m hshift
  have hB:MeasurableSet {J:SphericalModel.Disorder N P|
      (2*((j:ℝ)+2)*(p.val.val:ℝ)^j*Real.sqrt p.val.val+1+(p.val.val:ℝ)^j*K)*Real.sqrt N ≤
        unitJetEnvelope N p.val.val j (J p)}:=by
    have hh:=((unitEnvelope_lipschitz (p:=p.val.val) (j:=j) hN).continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _:TensorIndex N p.val.val=>ℝ)).symm.continuous.measurable.comp
        (show Measurable (fun J:SphericalModel.Disorder N P=>J p) from measurable_pi_apply p)))
    exact measurableSet_le measurable_const hh
  rw [sourceCoefficientKernel_affine A w,map_measureReal_apply (by fun_prop) hB]
  convert ht using 1
  congr 1

end
end SlowEquilibration.PairConditionalDeterminantMoments
