-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCountDecay
public import SlowEquilibration.SphericalLatitudeMaximumExclusion

@[expose] public section

/-! A genuine sharp strong-field lower bound for the maximum of the literal
affine tensor field. The low-maximum event is exponentially unlikely; no
Parisi formula, pressure limit, count bound or maximum estimate is assumed. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalKacRiceGluing SlowEquilibration.WholeFieldRegression
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual strong-field ground-state lower tail, uniform over every
admissible deterministic axis and orthogonal latitude frame. -/
theorem latitude_strongField_low_maximum_exponential (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε : ℝ} (hε : 0 < ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)), ‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)), (∀ x, inner ℝ (e x) w=0) →
        disorderLaw (n+3) μ.maxDegree
          {J | ∀ y, ‖y‖^2=((n+2 : ℕ) : ℝ) →
            latitudeField c J w e q y ≤ ((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε)} ≤
          2*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let v := covariancePolynomial c 1
  have ha : 0 < a := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hv : 0 < v := by
    dsimp only [v,c]
    rw [covariancePolynomial_center_one, covariancePolynomial_mixture]
    exact μ.xi_pos hQ
  have hc : ∀ p, 0 ≤ c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0 < firstCovariance c 1 := by
    dsimp only [c]
    rw [firstCovariance_center, firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  obtain ⟨η,hη,hcount⟩ := latitude_actual_count_halfNegative_decay μ hQ hq0 hq1 hab hε
  let τ := (Real.sqrt a/2)^2/(2*v)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  refine ⟨min τ η, lt_min hτ hη, ?_⟩
  filter_upwards [hcount] with n hn
  intro w hw e he
  have hN : 0 ≤ ((n+3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := latitude_low_maximum_probability_le (by omega) c hc hfirst hv w hw e he hq1
    (southPole (n+1)) (southPole_norm_sq (n+1))
    (show 0 ≤ Real.sqrt a/2 by positivity) (((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε))
  have hlow : -((n+3 : ℕ) : ℝ)*(Real.sqrt a/2)=((n+3 : ℕ) : ℝ)*(-Real.sqrt a/2) := by ring
  have hrate : -((n+3 : ℕ) : ℝ)*(Real.sqrt a/2)^2/(2*v)= -τ*((n+3 : ℕ) : ℝ) := by dsimp only [τ]; ring
  change disorderLaw (n+3) μ.maxDegree _ ≤
    ENNReal.ofReal (Real.exp (-((n+3 : ℕ) : ℝ)*(Real.sqrt a/2)^2/(2*v)))+_ at hm
  rw [hlow, hrate] at hm
  apply hm.trans
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-τ*((n+3 : ℕ) : ℝ)))+
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := add_le_add_right (hn w hw e he) _
    _ ≤ ENNReal.ofReal (Real.exp (-min τ η*((n+3 : ℕ) : ℝ)))+
        ENNReal.ofReal (Real.exp (-min τ η*((n+3 : ℕ) : ℝ))) := by
      apply add_le_add <;> apply ENNReal.ofReal_le_ofReal <;> apply Real.exp_le_exp.mpr
      · nlinarith [mul_le_mul_of_nonneg_right (min_le_left τ η) hN]
      · nlinarith [mul_le_mul_of_nonneg_right (min_le_right τ η) hN]
    _ = _ := (two_mul _).symm

/-- Equivalent explicit existence form: except on an exponentially small
set of actual tensor disorders, a point exceeds the sharp strong-field
height minus any specified positive tolerance. -/
theorem latitude_strongField_maximum_lower (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε : ℝ} (hε : 0 < ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)), ‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)), (∀ x, inner ℝ (e x) w=0) →
        disorderLaw (n+3) μ.maxDegree
          {J | ¬ ∃ y, ‖y‖^2=((n+2 : ℕ) : ℝ) ∧
            ((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε)<latitudeField c J w e q y} ≤
          2*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  simpa only [not_exists, not_and, not_lt] using
    latitude_strongField_low_maximum_exponential μ hQ hq0 hq1 hab hε

end
end SlowEquilibration.SphericalLatitudeChartKacRice
