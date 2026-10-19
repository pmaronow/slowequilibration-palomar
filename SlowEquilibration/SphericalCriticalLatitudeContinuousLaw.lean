-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorMaps
public import SlowEquilibration.SphericalTaylorResidualLaw

/-! The actual center field under value/radial/zero-gradient conditioning,
as a complete continuous Gaussian process on a compact latitude parameter
space. The affine mean is the true observation lift, and the centered law
is exactly the same for every prescribed mark. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalMarkedWindows GaussianContinuousFieldLaw
open scoped RealInnerProductSpace
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual finite center field on the specified compact parameter set. -/
def criticalContinuousField (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (z : K → Vector (n+1)) (hz : Continuous z) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] C(K,ℝ) :=
  modelContinuousField (centerCoefficients (mixtureCoefficients μ) Q) z hz

/-- The literal deterministic conditional mean, retaining the physical N
in the actual target (Ne,Nk,0). -/
def criticalContinuousMean (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z)
    (b : EuclideanSpace ℝ (Fin 2)) : C(K,ℝ) :=
  criticalContinuousField n μ Q z hz (scoreLift n μ Q u (((n+1 : ℕ) : ℝ) • b))

/-- The actual coefficient residual after both independent observations
have been removed. No prescribed mark appears in this map. -/
def criticalContinuousResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] C(K,ℝ) :=
  (criticalContinuousField n μ Q z hz).comp
    ((gradientResidual n μ Q u).comp (scoreResidual n μ Q u))

omit [CompactSpace K] in
theorem criticalContinuousMean_linear (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z)
    (b d : EuclideanSpace ℝ (Fin 2)) :
    criticalContinuousMean n μ Q u z hz (b+d)=
      criticalContinuousMean n μ Q u z hz b+criticalContinuousMean n μ Q u z hz d := by
  simp only [criticalContinuousMean,smul_add,map_add]

omit [CompactSpace K] in
/-- Pointwise affine decomposition of the actual posterior field. -/
theorem criticalContinuousField_posterior (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z)
    (b : EuclideanSpace ℝ (Fin 2)) (g : EuclideanDisorder (n+1) μ.maxDegree) :
    criticalContinuousField n μ Q z hz (mixedPosterior n μ Q u b g)=
      criticalContinuousResidual n μ Q u z hz g+criticalContinuousMean n μ Q u z hz b := by
  simp only [criticalContinuousResidual,criticalContinuousMean,mixedPosterior,
    ContinuousLinearMap.comp_apply,map_add]

/-- Full Borel continuous-process law of the centered actual conditioned
field, at every prescribed mixed mark and zero tangent gradient. -/
theorem actual_critical_centered_continuous_law (n : ℕ) (μ : FiniteMixture)
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (b : EuclideanSpace ℝ (Fin 2)) :
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map
      (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        criticalContinuousMean n μ Q u z hz b)=
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (criticalContinuousResidual n μ Q u z hz) := by
  have hm : Measurable (fun J : Disorder (n+1) μ.maxDegree =>
      criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        criticalContinuousMean n μ Q u z hz b) :=
    ((criticalContinuousField n μ Q z hz).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)).sub measurable_const
  have hp : Continuous (fun g => mixedPosterior n μ Q u b g) := by
    unfold mixedPosterior
    exact ((gradientResidual n μ Q u).continuous.comp
      (scoreResidual n μ Q u).continuous).add continuous_const
  have hp' : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q u b g)) :=
    (unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp.measurable
  rw [mixedConditionedLaw_eq_map n μ hQ hnp u hu b,
    Measure.map_map hm hp']
  congr 1
  funext g
  change criticalContinuousField n μ Q z hz (mixedPosterior n μ Q u b g)-
    criticalContinuousMean n μ Q u z hz b=criticalContinuousResidual n μ Q u z hz g
  rw [criticalContinuousField_posterior,add_sub_cancel_right]

/-- Exact centered latitude process law is independent of both conditioned
marks; this is an equality of measures on all continuous sample functions. -/
theorem actual_critical_centered_continuous_law_independent_marks (n : ℕ)
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (b d : EuclideanSpace ℝ (Fin 2)) :
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map
      (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        criticalContinuousMean n μ Q u z hz b)=
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu d).map
      (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        criticalContinuousMean n μ Q u z hz d) := by
  rw [actual_critical_centered_continuous_law n μ hQ hnp u hu z hz b,
    actual_critical_centered_continuous_law n μ hQ hnp u hu z hz d]

end
end SlowEquilibration.SphericalCriticalLatitude
