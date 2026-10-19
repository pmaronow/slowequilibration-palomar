-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeGuerra
public import SlowEquilibration.SphericalQuenchedEndpoint
public import SlowEquilibration.SphericalLatitudeCovariance

@[expose] public section

/-! The actual planted latitude pressure upper estimate of Section 13.
Every partition is the genuine affine-latitude restriction of the original
mixed tensor Hamiltonian. The thermodynamic upper is proved from finite-volume
Gaussian interpolation and the exact Gaussian-shell linear endpoint. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def latitudeLimitingVariance (μ : FiniteMixture) (β q : ℝ) : ℝ :=
  β^2*(1-q^2)*μ.xi1 q

theorem latitudeLimitingVariance_nonneg (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Icc 0 1) : 0 ≤ latitudeLimitingVariance μ β q := by
  have hs : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hs) (mixture_first_derivative_nonneg μ hq.1)

theorem latitudeLinearVariance_tendsto (μ : FiniteMixture) (β q : ℝ) :
    Tendsto (fun n : ℕ => latitudeLinearVariance n μ β q) atTop
      (𝓝 (latitudeLimitingVariance μ β q)) := by
  have hc : Tendsto (fun n : ℕ => latitudeLimitingVariance μ β q*(1+1/(n : ℝ)))
      atTop (𝓝 (latitudeLimitingVariance μ β q)) := by
    have hi : Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hs : Tendsto (fun n : ℕ => 1+1/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hi
    simpa only [mul_one] using hs.const_mul (latitudeLimitingVariance μ β q)
  apply hc.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold latitudeLinearVariance latitudeLimitingVariance
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

def latitudePressureTrial (μ : FiniteMixture) (β q : ℝ) : ℝ :=
  (β^2*(μ.xi 1-μ.xi q)+q-Real.log (1+q))/2

theorem latitude_linear_trial_eval (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : 0 ≤ q) :
    quenchedLinearTrial (latitudeLimitingVariance μ β q) (1+q)+
      β^2/2*(μ.xi 1-μ.xi q-(1-q)*μ.xi1 q) = latitudePressureTrial μ β q := by
  have hz : 1+q ≠ 0 := ne_of_gt (by linarith)
  unfold quenchedLinearTrial latitudeLimitingVariance latitudePressureTrial
  field_simp
  ring

theorem quenchedLinearTrial_nonneg {κ z : ℝ} (hκ : 0 ≤ κ) (hz : 1 ≤ z) :
    0 ≤ quenchedLinearTrial κ z := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hl := Real.log_le_sub_one_of_pos hz0
  have hd := div_nonneg hκ hz0.le
  unfold quenchedLinearTrial
  linarith

/-- The true thermodynamic upper for a normalized latitude section, uniform
over all physical centers and orthogonal tangent frames. -/
theorem latitudeQuenchedPressure_eventually_upper_of_tangent
    (μ : FiniteMixture) (β : ℝ) {q : ℝ} (hq : q ∈ Icc 0 1)
    (htangent : ∀ t ∈ Icc (-1 : ℝ) 1,
      μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε := by
  have hz : 1 ≤ 1+q := by linarith [hq.1]
  have hκ := latitudeLimitingVariance_nonneg μ β hq
  have hlin := linearSphereQuenchedPressure_eventually_upper_of_variance_tendsto
    (fun n => latitudeLinearVariance n μ β q) hκ hz
    (.of_forall fun n => latitudeLinearVariance_nonneg n μ β hq)
    (latitudeLinearVariance_tendsto μ β q) hε
  have ht : 0 ≤ quenchedLinearTrial (latitudeLimitingVariance μ β q) (1+q)+ε :=
    le_of_lt (add_pos_of_nonneg_of_pos (quenchedLinearTrial_nonneg hκ hz) hε)
  filter_upwards [hlin, eventually_ge_atTop 1] with n hlin hn
  intro u hu e he
  have hN0 : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hα0 : 0 ≤ (n : ℝ)/((n+1 : ℕ) : ℝ) := by positivity
  have hα1 : (n : ℝ)/((n+1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_one hN0).mpr
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hm := mul_le_mul_of_nonneg_left hlin hα0
  have hb := mul_le_mul_of_nonneg_right hα1 ht
  simp only [one_mul] at hb
  have hc := latitudeQuenchedPressure_le_linearTrial hn μ β hq htangent u hu e he
  have heval := latitude_linear_trial_eval μ β hq.1
  linarith

/-- All mixtures, including odd degrees, satisfy the actual planted-section
comparison for q at least one half. No positivity theorem is assumed. -/
theorem latitudeQuenchedPressure_eventually_upper (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Icc (1/2 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε :=
  latitudeQuenchedPressure_eventually_upper_of_tangent μ β ⟨by linarith [hq.1], hq.2⟩
    (fun t ht => μ.xi_latitude_tangent_le hq ht) hε

/-- Even mixtures satisfy the same genuine latitude upper on every
nonnegative latitude, with covariance convexity proved from the coefficients. -/
theorem latitudeQuenchedPressure_eventually_upper_of_even (μ : FiniteMixture) (β : ℝ)
    (heven : ∀ p ∈ μ.coeff.support, Even p) {q : ℝ} (hq : q ∈ Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε := by
  apply latitudeQuenchedPressure_eventually_upper_of_tangent μ β hq _ hε
  intro t ht
  have hs : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  have harg : q^2+(1-q^2)*t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg hs (by linarith [ht.1] : 0 ≤ t+1),
      mul_nonneg hs (by linarith [ht.2] : 0 ≤ 1-t)]
  exact convex_covariance_supporting_line μ (μ.convexOn_xi_Icc_of_even heven)
    ⟨by linarith [hq.1], hq.2⟩ harg

def plantedLatitudeQuenchedPressure (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) : ℝ :=
  (∫ J : Disorder (n+1) μ.maxDegree, Real.log (partitionAgainst (latitudeLaw u e q) β
    (field (mixtureCoefficients μ) (J+plantedShift (mixtureCoefficients μ) β u)))
      ∂disorderLaw (n+1) μ.maxDegree) / ((n+1 : ℕ) : ℝ)

theorem plantedLatitudeQuenchedPressure_eq {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    plantedLatitudeQuenchedPressure n μ β u e q = β^2*μ.xi q+latitudeQuenchedPressure n μ β u e q := by
  have hi := logPartitionAgainst_disorder_integrable (by omega) (latitudeLaw u e q)
    ((latitudeLaw_support hn u hu e he hq).mono (fun _ hx => hx.1))
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)
    (by rw [covariancePolynomial_mixture]; exact μ.xi_pos (by norm_num)) hβ
  unfold plantedLatitudeQuenchedPressure latitudeQuenchedPressure
  rw [integral_congr_ae (.of_forall fun J => latitude_logPartition_plantedShift hn _
    (mixtureCoefficients_nonnegative μ) β u hu e he hq J), integral_add (integrable_const _) hi]
  simp only [integral_const, probReal_univ, one_smul, covariancePolynomial_mixture]
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rfl

/-- The actual planted latitude upper, before inserting its proved coarea
entropy into a full-sphere band or cap integral. -/
theorem plantedLatitudeQuenchedPressure_eventually_upper (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 < β) {q : ℝ} (hq : q ∈ Icc (1/2 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeQuenchedPressure n μ β u e q ≤
        (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+ε := by
  filter_upwards [latitudeQuenchedPressure_eventually_upper μ β hq hε,
    eventually_ge_atTop 1] with n hn hdim
  intro u hu e he
  have hh := hn u hu e he
  rw [plantedLatitudeQuenchedPressure_eq hdim μ hβ u hu e he
    (abs_le.mpr ⟨by linarith [hq.1], hq.2⟩)]
  unfold latitudePressureTrial at hh
  linarith

end
end SlowEquilibration.SphericalModel
