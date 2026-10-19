-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeOriginalMeanEvent
public import SlowEquilibration.EntranceLatitudePosteriorMean

/-! Source 8.2 genuine mixed conditional latitude tangent mean estimate.
The original disorder event is explicit and exponentially likely; the
true posterior uses its own actual value/radial/gradient observations.
Every constant depends on the fixed model, Q and compact mark bound. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows SphericalPosteriorMaps
open SphericalLatitudeTensorMoments ConditionedEntrance
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem correction_uniform_constant_nonneg (p : ℕ) :
    0≤latitudeCorrectionUniformConstant p := by
  unfold latitudeCorrectionUniformConstant
  apply Finset.sum_nonneg
  intro S hS
  apply List.sum_nonneg
  intro a ha
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp ha
  positivity

/-- Literal model-only center observation constant. -/
def sourceLatitudeCenterConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  derivativeConstant (centerCoefficients (mixtureCoefficients μ) Q)

/-- A source8.2 mean constant fixed from the actual model and compact
mark bound before dimension or axis is chosen. -/
def sourceLatitudeMeanConstant (μ : FiniteMixture) (Q M : ℝ) : ℝ :=
  1+originalLatitudeLeadingConstant μ+originalLatitudeCorrectionConstant μ+
    regressionOrderConstant μ Q*(M+sourceLatitudeCenterConstant μ Q)

/-- Center observations are the actual seed's center field and radial
jet, with the same original regularity event for every physical axis. -/
theorem source_latitude_center_observations {n : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
    |field (centerCoefficients (mixtureCoefficients μ) Q) J u|≤ sourceLatitudeCenterConstant μ Q*((n+1 : ℕ) : ℝ) ∧
    |jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u (fun _ => u) J|≤
      sourceLatitudeCenterConstant μ Q*((n+1 : ℕ) : ℝ) := by
  unfold sourceLatitudeCenterConstant
  have hun := SphericalAging.LandscapeDerivatives.sphere_norm u hu
  have hb := field_regularDisorder_ball_bounds (by omega)
    (centerCoefficients (mixtureCoefficients μ) Q) J hJ u hun.le
  refine ⟨hb.1,?_⟩
  rw [jet,iteratedFDeriv_one_apply,←inner_gradient_left]
  apply (abs_real_inner_le_norm _ _).trans
  rw [hun]
  apply (mul_le_mul_of_nonneg_right hb.2.1 (Real.sqrt_nonneg _)).trans_eq
  rw [mul_assoc,Real.mul_self_sqrt (by positivity : (0 : ℝ)≤((n+1 : ℕ) : ℝ))]

private theorem normalized_source_mean_derivative_abs_le {n : ℕ} (μ : FiniteMixture) (Q : ℝ)
    {M A B r : ℝ} (hM : 0≤M) (hA : |A|≤M*((n+1 : ℕ) : ℝ))
    (hB : |B|≤M*((n+1 : ℕ) : ℝ)) (hr : |r|≤1) :
    |(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
      (valueThetaDerivative μ Q r*A+radialThetaDerivative μ Q r*B)|≤
      regressionOrderConstant μ Q*M*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1) := by
  have hs : 0<Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hC0 := (regressionOrderConstant_pos μ Q).le
  have ht := (mixed_regression_orders μ Q hr).2.1
  have ht' : |valueThetaDerivative μ Q r|+|radialThetaDerivative μ Q r|≤
      regressionOrderConstant μ Q*|r|^(μ.minDegree-1) := by linarith [abs_nonneg (tangentTheta μ Q r)]
  have hab : |valueThetaDerivative μ Q r*A+radialThetaDerivative μ Q r*B|≤
      regressionOrderConstant μ Q*|r|^(μ.minDegree-1)*(M*((n+1 : ℕ) : ℝ)) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    calc
      _≤|valueThetaDerivative μ Q r| *(M*((n+1 : ℕ) : ℝ))+
        |radialThetaDerivative μ Q r| *(M*((n+1 : ℕ) : ℝ)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
      _=(|valueThetaDerivative μ Q r|+|radialThetaDerivative μ Q r|)*(M*((n+1 : ℕ) : ℝ)) := by ring
      _≤_ := mul_le_mul_of_nonneg_right ht' (by positivity)
  have hw0 : 0≤(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ) := div_nonneg (by nlinarith [abs_le.mp hr]) hs.le
  have hw : (1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)≤1/Real.sqrt ((n+1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right (by nlinarith) hs.le
  rw [abs_mul,abs_of_nonneg hw0]
  apply (mul_le_mul hw hab (abs_nonneg _) (by positivity)).trans_eq
  have hn := Real.mul_self_sqrt (show (0 : ℝ)≤((n+1 : ℕ) : ℝ) by positivity)
  field_simp
  nlinarith [congrArg (fun s : ℝ => regressionOrderConstant μ Q*M*|r|^(μ.minDegree-1)*s) hn]

/-- Genuine conditional original-field tangent mean on the actual seed
Gaussian event, uniformly in physical axis, latitude and bounded marks. -/
theorem actual_mixedPosterior_latitudeObservableMean_uniform_bound {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    {M : ℝ} (hM : 0≤M) (J : Disorder (n+1) μ.maxDegree)
    (hJ : J∈originalLatitudeMeanGood n μ) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {e k r : ℝ} (he : |e|≤M) (hk : |k|≤M) (hr : r∈Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (mixtureCoefficients μ)
      (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) (euclideanDisorder J)))
      u (latitudeFrameAt u) r|≤
      sourceLatitudeMeanConstant μ Q M*(Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+1) := by
  have hobs := source_latitude_center_observations μ Q J hJ.1 u hu
  have hc0 : 0<sourceLatitudeCenterConstant μ Q := derivativeConstant_pos _
  have hmark (a : ℝ) (ha : |a|≤M) (b : ℝ) (hb : |b|≤ sourceLatitudeCenterConstant μ Q*((n+1 : ℕ) : ℝ)) :
      |((n+1 : ℕ) : ℝ)*a-b|≤(M+sourceLatitudeCenterConstant μ Q)*((n+1 : ℕ) : ℝ) := by
    have hab : |((n+1 : ℕ) : ℝ)*a-b|≤|((n+1 : ℕ) : ℝ)*a|+|b| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (((n+1 : ℕ) : ℝ)*a) 0 b
    apply hab.trans
    rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤((n+1 : ℕ) : ℝ))]
    apply (add_le_add (mul_le_mul_of_nonneg_left ha (by positivity)) hb).trans_eq
    ring
  have hc := normalized_source_mean_derivative_abs_le μ Q (add_nonneg hM hc0.le)
    (hmark e he _ hobs.1) (hmark k hk _ hobs.2) (abs_lt.mpr hr).le
  rw [actual_mixedPosterior_latitudeObservableMean hn μ hQ hnp u hu e k (euclideanDisorder J) hr,
    unpack_euclideanDisorder]
  apply (abs_add_le _ _).trans
  apply (add_le_add (actual_original_latitudeObservableMean_uniform_bound hn μ J hJ u hu hr) hc).trans
  have hl0 : 0≤originalLatitudeLeadingConstant μ := by
    unfold originalLatitudeLeadingConstant
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) (blockThreshold_pos p).le)
  have hh0 : 0≤originalLatitudeCorrectionConstant μ := by
    unfold originalLatitudeCorrectionConstant
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (Real.sqrt_nonneg _) (correction_uniform_constant_nonneg _))
  have ht0 := (regressionOrderConstant_pos μ Q).le
  have hv0 : 0≤Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1) := by positivity
  have htk0 : 0≤regressionOrderConstant μ Q*(M+sourceLatitudeCenterConstant μ Q) :=
    mul_nonneg ht0 (add_nonneg hM hc0.le)
  unfold sourceLatitudeMeanConstant
  nlinarith [mul_nonneg hh0 hv0]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
