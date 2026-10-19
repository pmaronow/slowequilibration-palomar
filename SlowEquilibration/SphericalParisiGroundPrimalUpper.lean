-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiGroundDualAllDegrees
public import SlowEquilibration.SphericalParisiGlobalPrimalDual
public import SlowEquilibration.SphericalParisiPositivePolynomialCalculus
public import SlowEquilibration.SphericalParisiSphereNetMeanTail

@[expose] public section

/-! Actual source one-step Huang--Sellke upper in the literal positive
piecewise-affine primal functional, including alpha=0 and genuine constant,
linear and odd covariance blocks. The physical pressure/REM/net proof and
actual global primal minimizer are consumed as proved theorems. -/

namespace SlowEquilibration.SphericalParisiGroundPrimalUpper
noncomputable section
open MeasureTheory Set Filter
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiGroundRSUpper
open SphericalParisiGroundConstantAllowance SphericalParisiPositivePolynomialCalculus
open SphericalParisiGroundDualAllDegrees SphericalParisiGlobalPrimalDual LatitudeGroundTrial
open scoped Topology BigOperators
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem xi2_nonnegative (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ xi2 d c t := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (mul_nonneg (hc i) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (pow_nonneg ht _)

omit [DecidableEq σ] in
theorem literal_functional_nonnegative (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) {L α s : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) :
    0 ≤ functional (xi1 d c) (xi2 d c) L α s := by
  have hL : 0 < L := by linarith [mul_nonneg hα (sub_nonneg.mpr hs.2)]
  have hprofile : ∀ t ∈ Icc (0 : ℝ) 1,0 < profile L α s t :=
    fun t ht => hb.trans_le (profile_lower hα hs ht)
  have henergy : 0 ≤ ∫ t in (0 : ℝ)..1,xi2 d c t*profile L α s t :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => mul_nonneg (xi2_nonnegative d c hc ht.1) (hprofile t ht).le)
  have hinverse : 0 ≤ ∫ t in (0 : ℝ)..1,(profile L α s t)⁻¹ :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => inv_nonneg.mpr (hprofile t ht).le)
  unfold functional
  exact div_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (xi1_zero_nonnegative d c hc) hL.le) henergy) hinverse) (by norm_num)

omit [DecidableEq σ] in
theorem functional_zero_alpha_eq (d : σ → ℕ) (c : σ → ℝ) (L s : ℝ) :
    functional (xi1 d c) (xi2 d c) L 0 s=(L*xi1 d c 1+1/L)/2 := by
  have he := energy_integral (xi d c) (xi1 d c) (xi2 d c)
    (xi_hasDerivAt d c) (xi1_hasDerivAt d c) (xi2_continuous d c)
    (s := 0) (by constructor <;> norm_num) L 0
  simp only [profile,zero_mul,sub_zero,add_zero] at he
  unfold functional
  simp only [profile,zero_mul,sub_zero]
  rw [he]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  ring

/-- Every literal constant profile gives its true finite physical ground
upper, with arbitrary nonnegative degrees. -/
theorem actual_constant_profile_ground_upper_all_degrees {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) {L : ℝ} (hL : 0 < L) :
    (∫ g,actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
      (N : ℝ)*(L*xi1 d c 1+1/L)/2 := by
  have hweighted : (∑ i,(d i : ℝ)*c i)=xi1 d c 1 := by
    simp only [xi1,one_pow,mul_one]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRS := actual_expected_maximum_le_all_degrees hN d c hc
  rw [hweighted] at hRS
  have hs : 0 ≤ xi1 d c 1 := xi1_nonnegative d c hc (by norm_num)
  have hroot := Real.sq_sqrt hs
  have hsq := sq_nonneg (L*Real.sqrt (xi1 d c 1)-1)
  have htrial : Real.sqrt (xi1 d c 1) ≤ (L*xi1 d c 1+1/L)/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have he : (L*xi1 d c 1+1/L)*L=L^2*xi1 d c 1+1 := by field_simp [hL.ne']
    have hw := congrArg (fun a : ℝ => L^2*a) hroot
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith [hw]
  exact hRS.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left htrial (Nat.cast_nonneg N))

/-- The genuine Gaussian spherical maximum is asymptotically bounded
by every literal source one-step positive-profile trial. All covariance
terms, including random constants, linear terms and odd degrees, are
actual finite ordered-tensor blocks. No HS or pressure formula is assumed. -/
theorem eventual_actual_ground_functional_upper_all_degrees
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s ∈ Icc (0 : ℝ) 1)
    (hb : 0 < L-α*(1-s)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        functional (xi1 d c) (xi2 d c) L α s+ε := by
  by_cases hαpos : 0 < α
  · by_cases h1 : 0 < xi1 d c 1
    · obtain ⟨q,hq,κ,_hκ,hmargin,hBelow⟩ := exists_dual_below_all_primal d c hαpos
        (xi_hasDerivAt d c) (xi_monotoneOn_unitInterval d c hc) h1 (xi1_zero_nonnegative d c hc)
      have hF := functional_eq_primal (xi d c) (xi1 d c) (xi2 d c)
        (xi_hasDerivAt d c) (xi1_hasDerivAt d c) (xi2_continuous d c) hαpos hs hb
      have hBelowF := hBelow s hs L hb
      rw [← hF] at hBelowF
      exact (eventual_actual_ground_oneStepDual_upper_all_degrees d c hc hαpos hq.1 hq.2 hmargin hε).mono
        (fun _ hN => by linarith [hBelowF])
    · have hz : xi1 d c 1=0 := le_antisymm (not_lt.mp h1)
        (xi1_nonnegative d c hc (by norm_num))
      have hF := literal_functional_nonnegative d c hc hα hs hb
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      have HRS := actual_expected_maximum_le_all_degrees hN d c hc
      have hweighted : (∑ i,(d i : ℝ)*c i)=xi1 d c 1 := by
        simp only [xi1,one_pow,mul_one]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hweighted,hz,Real.sqrt_zero,mul_zero] at HRS
      exact (div_nonpos_of_nonpos_of_nonneg HRS hNr.le).trans (by linarith)
  · have hzα : α=0 := le_antisymm (not_lt.mp hαpos) hα
    subst α
    rw [functional_zero_alpha_eq]
    have hL : 0 < L := by simpa only [zero_mul,sub_zero] using hb
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have H := actual_constant_profile_ground_upper_all_degrees hN d c hc hL
    have HD := div_le_div_of_nonneg_right H hNr.le
    have he : ((N : ℝ)*(L*xi1 d c 1+1/L)/2)/(N : ℝ)=(L*xi1 d c 1+1/L)/2 := by field_simp
    rw [he] at HD
    exact HD.trans (by linarith)

/-- Literal source one-step primal functional controls the true Gaussian
maximum in probability, without any Parisi or HS endpoint premise. -/
theorem actual_ground_functional_probability_tendsto_all_degrees
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s ∈ Icc (0 : ℝ) 1)
    (hb : 0 < L-α*(1-s)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(functional (xi1 d c) (xi2 d c) L α s+δ) < actualMaximum d c g})
      atTop (𝓝 (0 : ℝ)) := by
  exact SphericalParisiSphereNet.actual_ground_mean_upper_probability_tendsto d c hc
    (literal_functional_nonnegative d c hc hα hs hb)
    (fun ε hε => eventual_actual_ground_functional_upper_all_degrees d c hc hα hs hb hε) hδ

/-- Complete source theorem10.11: every actual admissible one-step
profile bounds the normalized maximum of the genuine finite Gaussian
spherical model. Positivity is the literal profile condition on[0,1]. -/
theorem actual_source_one_step_HuangSellke_upper
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {L α s : ℝ} (_hL : 0 < L) (hα : 0 ≤ α) (hs : s ∈ Icc (0 : ℝ) 1)
    (hprofile : ∀ t ∈ Icc (0 : ℝ) 1,0 < profile L α s t)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | functional (xi1 d c) (xi2 d c) L α s+δ < actualMaximum d c g/(N : ℝ)})
      atTop (𝓝 (0 : ℝ)) := by
  have hb : 0 < L-α*(1-s) := by
    have H := hprofile 1 ⟨by norm_num,le_rfl⟩
    rw [profile_of_ge hs.2] at H
    exact H
  have H := actual_ground_functional_probability_tendsto_all_degrees d c hc hα hs hb hδ
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq]
  rw [lt_div_iff₀ hNr,mul_comm]

end
end SlowEquilibration.SphericalParisiGroundPrimalUpper
