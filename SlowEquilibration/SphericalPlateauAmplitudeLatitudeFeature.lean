-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFeature
public import SlowEquilibration.SphericalPlateauAmplitudeScalar

@[expose] public section

/-! # Actual latitude features of the perturbed Gaussian bank

The genuine Euclidean feature Gram is the literal perturbed latitude
covariance at every amplitude, with its degree-zero normalization retained.
The Gaussian mean pressure is the actual bank-law latitude partition.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Metric
open SphericalModel
open scoped Topology BigOperators RealInnerProductSpace
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem frame_adjoint_center (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x,inner ℝ (e x) u=0) : e.toContinuousLinearMap.adjoint u=0 := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ u (e y)=inner ℝ (0 : Vector n) y
  rw [real_inner_comm,he]
  simp

theorem frame_adjoint_apply (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (x : Vector n) :
    e.toContinuousLinearMap.adjoint (e x)=x := by
  have hh := congrArg (fun T : Vector n →L[ℝ] Vector n => T x) e.adjoint_comp_self
  change e.toContinuousLinearMap.adjoint (e.toContinuousLinearMap x)=x
  simpa only [ContinuousLinearMap.comp_apply,one_apply_eq_self] using hh

theorem frame_adjoint_latitudeMap (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x,inner ℝ (e x) u=0) (r : ℝ) (x : Vector n) :
    e.toContinuousLinearMap.adjoint (latitudeMap u e r x)=
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)) • x := by
  rw [latitudeMap,map_add,map_smul,map_smul,frame_adjoint_center u e he,frame_adjoint_apply]
  simp

/-- Exact Gram of the actual flattened independent bank features on the
whole ambient space, with no covariance-in-law premise. -/
theorem amplitudeBankFeature_inner (μ : FiniteMixture) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (x y : Vector (n+1)) :
    inner ℝ (amplitudeBankFeature μ u e p₀ s x) (amplitudeBankFeature μ u e p₀ s y)=
      ∑ i : BankIndex μ,bankAmplitude p₀ s i^2*bankComponentKernel μ u e i x y := by
  simp only [amplitudeBankFeature,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  conv_lhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun I : SphericalAging.FiniteModel.TensorIndex n i.2.val =>
      (bankAmplitude p₀ s i*bankComponentScale μ u i y*
        SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint y) I)*
      (bankAmplitude p₀ s i*bankComponentScale μ u i x*
        SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint x) I))=
      fun I => (bankAmplitude p₀ s i^2*bankComponentScale μ u i x*bankComponentScale μ u i y)*
        (SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint x) I*
          SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint y) I) := by
    funext I;ring
  rw [heq,← Finset.mul_sum,SphericalAging.FiniteModel.tensorMonomial_gram]
  unfold bankComponentKernel
  ring

def amplitudeLatitudeBankFeature (μ : FiniteMixture) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (r : ℝ) (x : Vector n) : EuclideanBank n μ :=
  amplitudeBankFeature μ u e p₀ s (latitudeMap u e r x)

def amplitudeLatitudeBankLinear (μ : FiniteMixture) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (r : ℝ) (x : Vector n) : EuclideanBank n μ →L[ℝ] ℝ :=
  innerSL ℝ (amplitudeLatitudeBankFeature μ u e p₀ s r x)

theorem amplitudeLatitudeBankFeature_continuous (μ : FiniteMixture) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ) :
    Continuous (amplitudeLatitudeBankFeature μ u e p₀ s r) :=
  (amplitudeBankFeature_continuous μ u e p₀ s).comp (latitudeMap_continuous u e r)

theorem amplitudeLatitudeBankLinear_continuous (μ : FiniteMixture) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ) :
    Continuous (amplitudeLatitudeBankLinear μ u e p₀ s r) :=
  (innerSL ℝ).continuous.comp (amplitudeLatitudeBankFeature_continuous μ u e p₀ s r)

/-- The actual Gram on the literal latitude has exactly the stated
amplitude covariance polynomial, including transverse degree zero. -/
theorem amplitudeLatitudeBankFeature_inner (hn : 1≤n) (μ : FiniteMixture)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) {r : ℝ} (hr : |r|≤1) (x y : Vector n) :
    inner ℝ (amplitudeLatitudeBankFeature μ u e p₀ s r x) (amplitudeLatitudeBankFeature μ u e p₀ s r y)=
      ((n+1 : ℕ) : ℝ)*amplitudeLatitudeCovariance μ p₀ s r (overlap x y) := by
  have hn0 : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hN0 : ((n+1 : ℕ) : ℝ)≠0 := by positivity
  have hs : (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)))^2=
      ((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2) := Real.sq_sqrt (by
        have hr2 : 0≤1-r^2 := by nlinarith [abs_le.mp hr]
        positivity)
  unfold amplitudeLatitudeBankFeature
  rw [amplitudeBankFeature_inner]
  unfold amplitudeLatitudeCovariance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [bankComponentKernel_eq,frame_adjoint_latitudeMap u e he,frame_adjoint_latitudeMap u e he,
    real_inner_smul_left,real_inner_smul_right]
  have hrx : overlap u (latitudeMap u e r x)=r := by
    rw [show overlap u (latitudeMap u e r x)=overlap (latitudeMap u e r x) u by unfold overlap;rw [real_inner_comm]]
    exact overlap_latitude_center u hu e he r x
  have hry : overlap u (latitudeMap u e r y)=r := by
    rw [show overlap u (latitudeMap u e r y)=overlap (latitudeMap u e r y) u by unfold overlap;rw [real_inner_comm]]
    exact overlap_latitude_center u hu e he r y
  rw [hrx,hry]
  have harg : (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*
      (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*inner ℝ x y))/(n+1 : ℝ)=
        (1-r^2)*overlap x y := by
    rw [show Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*
        (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*inner ℝ x y)=
        (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)))^2*inner ℝ x y by ring,hs]
    unfold overlap
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
  rw [harg,mul_pow,show r^(i.1.val.val-i.2.val)*r^(i.1.val.val-i.2.val)=r^(2*(i.1.val.val-i.2.val)) by
    rw [← pow_two,← pow_mul]
    congr 1
    omega]
  rw [mul_pow (1-r^2) (overlap x y) i.2.val]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

/-- Literal bank-law quenched latitude pressure, retaining every original
Gaussian tensor and every perturbed source amplitude. -/
def amplitudeLatitudeQuenchedPressure (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r : ℝ) : ℝ :=
  (∫D,Real.log (partitionAgainst (latitudeLaw u e r) β (amplitudeField μ u e p₀ s D))
    ∂bankLaw n μ)/((n+1 : ℕ) : ℝ)

/-- Exact partition identification under the true Euclidean bank map. -/
theorem amplitudeLatitude_gaussianMoment_eq_partition (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r : ℝ) (w : EuclideanBank n μ) :
    GaussianSpinInterpolation.moment (sphereLaw n) (fun _ => 1)
      (amplitudeLatitudeBankLinear μ u e p₀ s r) (β • w)=
      partitionAgainst (latitudeLaw u e r) β (amplitudeField μ u e p₀ s (unpackBankCLM n μ w)) := by
  unfold partitionAgainst latitudeLaw
  have hc : Continuous (fun x : Vector (n+1) => Real.exp (β*amplitudeField μ u e p₀ s (unpackBankCLM n μ w) x)) := by
    simpa only [Function.comp_def] using Real.continuous_exp.comp
      ((amplitudeField_contDiff μ u e p₀ s (unpackBankCLM n μ w)).continuous.const_mul β)
  rw [integral_map (latitudeMap_continuous u e r).measurable.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [GaussianSpinInterpolation.weight,map_smul,smul_eq_mul,one_mul,
      amplitudeLatitudeBankLinear,amplitudeLatitudeBankFeature,innerSL_apply_apply]
    have hh := amplitudeBankLinear_apply μ β u e p₀ s (latitudeMap u e r x) w
    simpa only [amplitudeBankLinear,smul_apply,smul_eq_mul,innerSL_apply_apply] using congrArg Real.exp hh

/-- The true Gaussian feature pressure is exactly the original bank-law
latitude pressure; all required Gaussian integrability is proved internally. -/
theorem amplitudeLatitudeQuenchedPressure_eq_gaussianMean (hn : 1≤n) (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r : ℝ) :
    amplitudeLatitudeQuenchedPressure n μ β u e p₀ s r=
      GaussianSpinInterpolation.averagedLogPartition (sphereLaw n)
        (amplitudeLatitudeBankLinear μ u e p₀ s r) β/((n+1 : ℕ) : ℝ) := by
  let L := amplitudeLatitudeBankLinear μ u e p₀ s r
  have hL : Continuous L := amplitudeLatitudeBankLinear_continuous μ u e p₀ s r
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Vector n) (Real.sqrt (n : ℝ))).exists_bound_of_continuousOn hL.continuousOn
  have hb : ∀ᵐ x ∂sphereLaw n,‖L x‖ ≤ max B 0 := by
    filter_upwards [sphereLaw_support hn] with x hx
    have hball : x∈closedBall (0 : Vector n) (Real.sqrt (n : ℝ)) := by
      simp only [mem_closedBall,dist_zero_right]
      rw [← hx,Real.sqrt_sq (norm_nonneg x)]
    exact (hB x hball).trans (le_max_left _ _)
  have hi := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw n) L hL.measurable
    (le_max_right _ _) hb β
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at hi
  have hm := (actual_bank_flattened_gaussian n μ).integral_comp hi.aestronglyMeasurable
  unfold amplitudeLatitudeQuenchedPressure GaussianSpinInterpolation.averagedLogPartition
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
  dsimp only [L] at hm
  rw [← hm]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun D => by
    simp only [Function.comp_apply,GaussianSpinInterpolation.logPartition,
      amplitudeLatitude_gaussianMoment_eq_partition,unpackBank_euclideanBank]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
