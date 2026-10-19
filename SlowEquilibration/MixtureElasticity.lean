-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixturePlateauLocation
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Actual finite-mixture derivative elasticity

The tilted masses come from the actual first derivative polynomial. Its
elasticity derivative is the genuine finite centered-square variance divided
by the radius. This proves monotonicity without an elasticity hypothesis.
-/

namespace SlowEquilibration.FiniteMixture

noncomputable section
open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem xi1_pos (μ : FiniteMixture) {r : ℝ} (hr : 0 < r) : 0 < μ.xi1 r := by
  unfold xi1
  apply Finset.sum_pos
  · intro p hp
    exact mul_pos (mul_pos (μ.coeff_pos hp)
      (Nat.cast_pos.mpr (by have := μ.degree_ge_two hp; omega))) (pow_pos hr _)
  · exact μ.support_nonempty

/-- Actual first-derivative tilted mass before normalization. -/
def firstRawWeight (μ : FiniteMixture) (r : ℝ) (p : ℕ) : ℝ :=
  μ.coeff p*(p : ℝ)*r^(p-1)

def firstTiltedWeight (μ : FiniteMixture) (r : ℝ) (p : ℕ) : ℝ :=
  μ.firstRawWeight r p/μ.xi1 r

def firstTiltedMean (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.firstTiltedWeight r p*((p-1 : ℕ) : ℝ)

def firstTiltedSecondMoment (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.firstTiltedWeight r p*((p-1 : ℕ) : ℝ)^2

/-- Genuine finite centered-square variance of the shifted first-derivative
degree, with its actual normalized polynomial masses. -/
def firstTiltedVariance (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support,
    μ.firstTiltedWeight r p*(((p-1 : ℕ) : ℝ)-μ.firstTiltedMean r)^2

theorem firstTiltedWeight_nonneg (μ : FiniteMixture) {r : ℝ} (hr : 0 < r) (p : ℕ) :
    0 ≤ μ.firstTiltedWeight r p := by
  exact div_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
    (pow_nonneg hr.le _)) (μ.xi1_pos hr).le

theorem firstTiltedWeight_sum (μ : FiniteMixture) {r : ℝ} (hr : 0 < r) :
    ∑ p ∈ μ.coeff.support, μ.firstTiltedWeight r p = 1 := by
  unfold firstTiltedWeight
  rw [← Finset.sum_div]
  exact div_self (μ.xi1_pos hr).ne'

private theorem euler_monomial (n : ℕ) (r : ℝ) :
    r*((n : ℝ)*r^(n-1)) = (n : ℝ)*r^n := by
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]; ring

private theorem euler2_monomial (n : ℕ) (r : ℝ) :
    r^2*((n : ℝ)*((n-1 : ℕ) : ℝ)*r^(n-2)) =
      (n : ℝ)*((n : ℝ)-1)*r^n := by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp [pow_succ]; ring

theorem scaled_xi2_first (μ : FiniteMixture) (r : ℝ) :
    r*μ.xi2 r = ∑ p ∈ μ.coeff.support,
      μ.firstRawWeight r p*((p-1 : ℕ) : ℝ) := by
  unfold xi2 curvatureCoeff firstRawWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hexp : p-2 = (p-1)-1 := by omega
  rw [hexp]
  calc
    _ = μ.coeff p*(p : ℝ)*(r*(((p-1 : ℕ) : ℝ)*r^(p-1-1))) := by ring
    _ = _ := by rw [euler_monomial]; ring

theorem scaled_v1_first (μ : FiniteMixture) (r : ℝ) :
    r^2*μ.v1 r = ∑ p ∈ μ.coeff.support,
      μ.firstRawWeight r p*((p-1 : ℕ) : ℝ)*(((p-1 : ℕ) : ℝ)-1) := by
  unfold v1 curvatureCoeff firstRawWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hexp : p-2-1 = (p-1)-2 := by omega
  have hfac : p-2 = (p-1)-1 := by omega
  rw [hexp, hfac]
  calc
    _ = μ.coeff p*(p : ℝ)*(r^2*(((p-1 : ℕ) : ℝ)*
      ((p-1-1 : ℕ) : ℝ)*r^(p-1-2))) := by ring
    _ = _ := by rw [euler2_monomial]; ring

/-- The elasticity of the actual first derivative polynomial. -/
def elasticity (μ : FiniteMixture) (r : ℝ) : ℝ := r*μ.xi2 r/μ.xi1 r

theorem firstTiltedMean_eq_elasticity (μ : FiniteMixture) (r : ℝ) :
    μ.firstTiltedMean r = μ.elasticity r := by
  unfold firstTiltedMean firstTiltedWeight elasticity
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← μ.scaled_xi2_first r]

theorem firstTiltedVariance_eq_second_sub_sq (μ : FiniteMixture) {r : ℝ} (hr : 0 < r) :
    μ.firstTiltedVariance r = μ.firstTiltedSecondMoment r-μ.firstTiltedMean r^2 := by
  unfold firstTiltedVariance
  have hexpand : ∀ p : ℕ,
      μ.firstTiltedWeight r p*(((p-1 : ℕ) : ℝ)-μ.firstTiltedMean r)^2 =
      μ.firstTiltedWeight r p*((p-1 : ℕ) : ℝ)^2-
        2*μ.firstTiltedMean r*(μ.firstTiltedWeight r p*((p-1 : ℕ) : ℝ))+
        μ.firstTiltedMean r^2*μ.firstTiltedWeight r p := by intro p; ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, μ.firstTiltedWeight_sum hr]
  change μ.firstTiltedSecondMoment r-2*μ.firstTiltedMean r*μ.firstTiltedMean r+
    μ.firstTiltedMean r^2*1 = _
  ring

theorem firstTiltedSecondMoment_eq (μ : FiniteMixture) (r : ℝ) :
    μ.firstTiltedSecondMoment r = r^2*μ.v1 r/μ.xi1 r+μ.firstTiltedMean r := by
  have hterm : ∀ p : ℕ,
      μ.firstTiltedWeight r p*((p-1 : ℕ) : ℝ)^2 =
      (μ.firstRawWeight r p*((p-1 : ℕ) : ℝ)*(((p-1 : ℕ) : ℝ)-1))/μ.xi1 r+
        μ.firstTiltedWeight r p*((p-1 : ℕ) : ℝ) := by
    intro p
    unfold firstTiltedWeight
    ring
  unfold firstTiltedSecondMoment
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← μ.scaled_v1_first r]
  rfl

theorem firstTiltedVariance_nonneg (μ : FiniteMixture) {r : ℝ} (hr : 0 < r) :
    0 ≤ μ.firstTiltedVariance r :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (μ.firstTiltedWeight_nonneg hr p) (sq_nonneg _))

/-- Genuine derivative identity: logarithmic elasticity increases by the
actual first-derivative degree variance divided by radius. -/
theorem elasticity_hasDerivAt (μ : FiniteMixture) {r : ℝ} (hr : 0 < r) :
    HasDerivAt μ.elasticity (μ.firstTiltedVariance r/r) r := by
  have h := ((hasDerivAt_id r).mul (μ.hasDerivAt_xi2 r)).div
    (μ.hasDerivAt_xi1 r) (μ.xi1_pos hr).ne'
  convert h using 1
  · ext s
    rfl
  · rw [μ.firstTiltedVariance_eq_second_sub_sq hr, μ.firstTiltedSecondMoment_eq,
      μ.firstTiltedMean_eq_elasticity]
    unfold elasticity
    dsimp only [id_eq, Pi.mul_apply]
    field_simp [(μ.xi1_pos hr).ne', hr.ne']
    ring

/-- Actual finite covariance elasticity is monotone on positive overlaps;
both parities and degree-two coefficients are included. -/
theorem elasticity_monotoneOn (μ : FiniteMixture) : MonotoneOn μ.elasticity (Ioi (0 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun r hr => (μ.elasticity_hasDerivAt hr).continuousAt.continuousWithinAt
  · intro r hr
    exact (μ.elasticity_hasDerivAt (by simpa using hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr0 : 0 < r := by simpa using hr
    rw [(μ.elasticity_hasDerivAt hr0).deriv]
    exact div_nonneg (μ.firstTiltedVariance_nonneg hr0) hr0.le

/-- The genuine derivative of the dynamical scalar away from zero. -/
theorem A_hasDerivAt (μ : FiniteMixture) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (Thresholds.A μ.xi)
      ((r*(1-r)*μ.xi2 r-μ.xi1 r)/r^2) r := by
  have h := (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).mul
    (μ.hasDerivAt_xi1 r)).div (hasDerivAt_id r) hr
  convert h using 1
  · ext s
    unfold Thresholds.A
    rw [(μ.hasDerivAt_xi s).deriv]
    rfl
  · dsimp only [id_eq, Pi.mul_apply, Pi.sub_apply]
    ring

/-- At the actual right endpoint, the genuine dynamical derivative is
nonpositive. This follows from its true right-hand tail and ordinary
derivative, including possible zero derivatives at the endpoint. -/
theorem A_derivative_qStar_nonpos (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    deriv (Thresholds.A μ.xi) (Thresholds.qStar μ.xi β) ≤ 0 := by
  let q := Thresholds.qStar μ.xi β
  have hq := (μ.qStar_solves_plateau hβ).1
  have hq' : q ∈ Ioo (0 : ℝ) 1 := hq
  have hlevel : β^2*Thresholds.A μ.xi q = 1 :=
    (Thresholds.plateau_iff hq).mpr (μ.qStar_solves_plateau hβ).2
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hderiv := (μ.A_hasDerivAt hq.1.ne').const_mul (β^2)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1-q :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1-q from eventually_lt_nhds
      (sub_pos.mpr hq'.2)).filter_mono nhdsWithin_le_nhds
  have hd : β^2*((q*(1-q)*μ.xi2 q-μ.xi1 q)/q^2) ≤ 0 := by
    apply le_of_tendsto hderiv.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
    have ht0 : 0 < t := ht
    have hqt : q+t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hq'.1], by linarith⟩
    have htail := μ.A_le_one_of_qStar_lt (β := β) hqt
      (show Thresholds.qStar μ.xi β < q+t by change q < q+t; linarith)
    change t⁻¹*(β^2*Thresholds.A μ.xi (q+t)-β^2*Thresholds.A μ.xi q) ≤ 0
    rw [hlevel]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr htail)
  rw [(μ.A_hasDerivAt hq.1.ne').deriv]
  nlinarith [sq_pos_of_pos hβpos]

/-- Endpoint elasticity bound derived from the actual plateau tail,
ordinary derivative, and positive first covariance derivative. -/
theorem elasticity_qStar_le (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    let q := Thresholds.qStar μ.xi β
    μ.elasticity q ≤ 1/(1-q) := by
  let q := Thresholds.qStar μ.xi β
  have hq := (μ.qStar_solves_plateau hβ).1
  have hd := μ.A_derivative_qStar_nonpos hβ
  rw [(μ.A_hasDerivAt hq.1.ne').deriv] at hd
  have hnum : q*(1-q)*μ.xi2 q-μ.xi1 q ≤ 0 := by
    simpa only [zero_mul] using (div_le_iff₀ (sq_pos_of_pos hq.1)).mp hd
  change q*μ.xi2 q/μ.xi1 q ≤ 1/(1-q)
  apply (div_le_div_iff₀ (μ.xi1_pos hq.1) (sub_pos.mpr hq.2)).mpr
  nlinarith

end

end SlowEquilibration.FiniteMixture
