-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeOriginalMeanPolynomial
public import SlowEquilibration.SphericalOriginalPosteriorSourceField

/-! Exact actual mixed posterior latitude mean and tangent mean. The
source tangent correction has zero latitude mean by actual odd latitude
moments; the value/radial corrections use the seed's true observations. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalGaussianJet SphericalLatitudeTensorMoments
open SphericalCriticalLatitude SphericalMarkedWindows SphericalPosteriorMaps
open ConditionedEntrance SphericalTwoPointCovariance SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual odd latitude moments give exactly zero mean for a tangent
linear field at its own conditioning axis. -/
theorem actual_latitude_tangent_linear_mean_zero {n : ℕ} (u G : Vector (n+1))
    (hG : inner ℝ G u=0) (r : ℝ) :
    (∫ v,inner ℝ G v ∂latitudeLaw u (latitudeFrameAt u) r)=0 := by
  have h := actual_latitude_centered_product_odd_zero u (latitudeFrameAt u) r
    ({(0 : Fin 1)} : Finset (Fin 1)) (by simp) (fun _ => G)
  simpa only [Finset.prod_singleton,inner_sub_right,real_inner_smul_right,hG,mul_zero,sub_zero] using h

private theorem latitude_field_integrable {n P : ℕ} (hn : 1≤n) (c : Degree P→ℝ)
    (J : Disorder (n+1) P) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {r : ℝ} (hr : |r|≤1) : Integrable (field c J) (latitudeLaw u (latitudeFrameAt u) r) := by
  apply Integrable.of_bound (field_contDiff c J).continuous.aestronglyMeasurable
    (sampleDerivativeConstant c J*((n+1 : ℕ) : ℝ))
  filter_upwards [latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr] with v hv
  rw [Real.norm_eq_abs]
  exact (field_sample_ball_bounds (by omega) c J v
    (SphericalAging.LandscapeDerivatives.sphere_norm v hv.1).le).1

private theorem latitude_linear_integrable {n : ℕ} (hn : 1≤n) (u G : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    Integrable (fun v => inner ℝ G v) (latitudeLaw u (latitudeFrameAt u) r) := by
  apply Integrable.of_bound (by fun_prop) (‖G‖*Real.sqrt ((n+1 : ℕ) : ℝ))
  filter_upwards [latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr] with v hv
  rw [Real.norm_eq_abs]
  simpa only [SphericalAging.LandscapeDerivatives.sphere_norm v hv.1] using abs_real_inner_le_norm G v

/-- Literal actual mixed posterior mean equals the original mean plus
its observed source value/radial correction. The tangent term integrates
to zero under the actual latitude law. -/
theorem actual_mixedPosterior_latitudeFieldMean {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e k : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) {r : ℝ} (hr : |r|≤1) :
    latitudeFieldMean (mixtureCoefficients μ)
      (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) u (latitudeFrameAt u) r=
      latitudeFieldMean (mixtureCoefficients μ) (unpackDisorder g) u (latitudeFrameAt u) r+
        valueTheta μ Q r*(((n+1 : ℕ) : ℝ)*e-
          field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g) u)+
        radialTheta μ Q r*(((n+1 : ℕ) : ℝ)*k-
          jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u (fun _ => u) (unpackDisorder g)) := by
  let J := unpackDisorder g
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let G := surfaceGradient (field cQ J) u
  let A := valueTheta μ Q r*(((n+1 : ℕ) : ℝ)*e-field cQ J u)+
    radialTheta μ Q r*(((n+1 : ℕ) : ℝ)*k-jet cQ 1 u (fun _ => u) J)
  have hG : inner ℝ G u=0 := by
    rw [real_inner_comm]
    dsimp only [G,surfaceGradient]
    rw [tangentProjection_apply]
    exact projection_tangent (by omega) u (gradient (field cQ J) u)
      ((SphericalAging.HardSphereDynamics.onSphere_iff_norm_sq u).mpr hu)
  have hi := latitude_linear_integrable hn u G hu hr
  have hA : Integrable (fun _ : Vector (n+1) => A) (latitudeLaw u (latitudeFrameAt u) r) := integrable_const A
  have he : (fun v => field (mixtureCoefficients μ)
      (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) v)=ᵐ[latitudeLaw u (latitudeFrameAt u) r]
      fun v => field (mixtureCoefficients μ) J v+(A-tangentTheta μ Q r*inner ℝ G v) := by
    filter_upwards [latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr] with v hv
    rw [show field (mixtureCoefficients μ)
      (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) v=
      field (mixtureCoefficients μ) J v+sourceRegressionCorrection μ Q hQ hnp J u e k v from
        actual_mixedPosterior_original_field n μ hQ hnp u hu e k g v]
    unfold sourceRegressionCorrection regressionCorrection
    rw [hv.2]
  unfold latitudeFieldMean
  have hic : Integrable (fun v => A-tangentTheta μ Q r*inner ℝ G v) (latitudeLaw u (latitudeFrameAt u) r) := by
    convert hA.sub (hi.const_mul (tangentTheta μ Q r)) using 1
  rw [integral_congr_ae he,integral_add (latitude_field_integrable hn (mixtureCoefficients μ) J u hu hr) hic]
  have hsi : (∫ v,A-tangentTheta μ Q r*inner ℝ G v ∂latitudeLaw u (latitudeFrameAt u) r)=
      (∫ _v : Vector (n+1),A ∂latitudeLaw u (latitudeFrameAt u) r)-
        (∫ v,tangentTheta μ Q r*inner ℝ G v ∂latitudeLaw u (latitudeFrameAt u) r) := by
    convert integral_sub hA (hi.const_mul (tangentTheta μ Q r)) using 1
  rw [hsi,integral_const,integral_const_mul,
    actual_latitude_tangent_linear_mean_zero u G hG,mul_zero,sub_zero]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  dsimp only [A,J,cQ]
  ring

/-- Exact actual posterior tangent mean, derived by differentiating the
true mean identity locally and by genuine all-sample latitude calculus. -/
theorem actual_mixedPosterior_latitudeObservableMean {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e k : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    latitudeObservableMean (mixtureCoefficients μ)
      (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) u (latitudeFrameAt u) r=
      latitudeObservableMean (mixtureCoefficients μ) (unpackDisorder g) u (latitudeFrameAt u) r+
        (1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
          (valueThetaDerivative μ Q r*(((n+1 : ℕ) : ℝ)*e-
            field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g) u)+
          radialThetaDerivative μ Q r*(((n+1 : ℕ) : ℝ)*k-
            jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u (fun _ => u) (unpackDisorder g))) := by
  let A := ((n+1 : ℕ) : ℝ)*e-field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g) u
  let B := ((n+1 : ℕ) : ℝ)*k-jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u (fun _ => u) (unpackDisorder g)
  have hd := ((actual_latitudeFieldMean_allDisorder_hasDerivAt hn (mixtureCoefficients μ)
    (unpackDisorder g) u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr).add
      ((valueTheta_hasDerivAt μ Q r).mul_const A)).add ((radialTheta_hasDerivAt μ Q r).mul_const B)
  have he : latitudeFieldMean (mixtureCoefficients μ)
      (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) u (latitudeFrameAt u)=ᶠ[𝓝 r]
      (fun t => latitudeFieldMean (mixtureCoefficients μ) (unpackDisorder g) u (latitudeFrameAt u) t+
        valueTheta μ Q t*A+radialTheta μ Q t*B) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact actual_mixedPosterior_latitudeFieldMean hn μ hQ hnp u hu e k g (abs_lt.mpr ht).le
  rw [actual_latitudeObservableMean_allDisorder_eq_radial_derivative hn _ _ u hu
    (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr,(hd.congr_of_eventuallyEq he).deriv]
  dsimp only [A,B]
  have hden : 1-r^2≠0 := (show 0<1-r^2 by nlinarith [hr.1,hr.2]).ne'
  have hs : Real.sqrt ((n+1 : ℕ) : ℝ)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp
  ring

end
end SlowEquilibration.EntranceLatitudeTangentObservable
