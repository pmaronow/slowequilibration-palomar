-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorCovarianceMajor
public import SlowEquilibration.PureResidualCoefficient
public import SlowEquilibration.SphericalSubcriticalOverlapMoment
public import SlowEquilibration.SphereSupportedIntegrals
public import SlowEquilibration.SphericalGuerraBound

/-! The source pure-cap residual covariance and its transverse angular
exponential moment have a single strict budget on every latitude above
the selected cap endpoint. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorAngularBudget
noncomputable section
open Set Filter MeasureTheory SphericalForm
open SphericalModel SphericalParisiPureLatitudeCovariance
open SphericalTAPCriticalPureLatitudeVariance
open PureStationarity SourcePureCapPosteriorCovarianceMajor
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pureResidualCoefficient_nonneg
    (p : ℕ) (hp : 2 ≤ p) (β a : ℝ) :
    0 ≤ pureResidualCoefficient p β a := by
  let k := p-2
  have hp' : p = k+2 := by dsimp [k]; omega
  rw [pureResidualCoefficient, hp', pureResidualAtOne_sum]
  apply mul_nonneg (sq_nonneg β)
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (pow_nonneg (sq_nonneg a) _)

/-- Source (9.33) uniformly on one fixed cap, with the cap's strict
residual coefficient as its true constant. -/
theorem pure_source_covariance_major_on_cap
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a q t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ico a 1) (ht : |t| ≤ 1) :
    |β^2*sourceValueTau (FiniteMixture.pure p hp 1 (by positivity)) 1 q t| ≤
      pureResidualCoefficient p β a*t^2 := by
  have hq' : q ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_le hq.1, hq.2⟩
  have hmajor := pure_source_covariance_major p hp 1 (by positivity) β
    (by norm_num : (0 : ℝ) < 1) hq' ht
  have hvar : β^2*sourcePureLatitudeVariance p 1 q =
      pureResidualCoefficient p β q := by
    rw [pureResidualCoefficient_eq p hp]
    unfold sourcePureLatitudeVariance
    ring
  simp only [one_pow, mul_one] at hmajor
  rw [hvar] at hmajor
  have hmono := pureResidualCoefficient_antitoneOn p hp β
    (show a ∈ Icc (0 : ℝ) 1 from ⟨ha.1.le,ha.2.le⟩)
    (show q ∈ Icc (0 : ℝ) 1 from ⟨hq'.1.le,hq'.2.le⟩) hq.1
  exact hmajor.trans (mul_le_mul_of_nonneg_right hmono (sq_nonneg t))

/-- The actual uniform-sphere transverse overlap integral is bounded
uniformly in the dimension, cap latitude, and transverse axis. This is
the angular integration half of source `pc-band-second`. -/
theorem pure_source_posterior_angular_exponential_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (x : Vector N), ‖x‖^2 = (N : ℝ) →
      ∀ q ∈ Ico a 1,
      (∫ y : Vector N,
          Real.exp ((N : ℝ)*β^2*
            sourceValueTau (FiniteMixture.pure p hp 1 (by positivity)) 1 q
              (overlap x y)) ∂sphereLaw N) ≤ C := by
  let b := pureResidualCoefficient p β a
  obtain ⟨C,hC,hCbound⟩ := sphere_overlap_exp_square_eventually_bounded
    (pureResidualCoefficient_nonneg p hp β a) hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound,Filter.eventually_ge_atTop 1] with N hN hNpos
  intro x hx q hq
  have hcont₁ : Continuous (fun y : Vector N =>
      Real.exp ((N : ℝ)*β^2*
        sourceValueTau (FiniteMixture.pure p hp 1 (by positivity)) 1 q
          (overlap x y))) := by
    simp only [pure_valueTau_eq_monomial p hp 1 (by positivity)
      (by norm_num : (0 : ℝ) < 1)]
    unfold overlap
    fun_prop
  have hcont₂ : Continuous (fun y : Vector N =>
      Real.exp (b*(N : ℝ)*(overlap x y)^2)) := by
    unfold overlap
    fun_prop
  have hInt₁ := integrable_sphereSupported_continuous (sphereLaw N)
    (sphereLaw_support hNpos) hcont₁
  have hInt₂ := integrable_sphereSupported_continuous (sphereLaw N)
    (sphereLaw_support hNpos) hcont₂
  calc
    _ ≤ ∫ y : Vector N,
        Real.exp (b*(N : ℝ)*(overlap x y)^2) ∂sphereLaw N := by
      apply integral_mono_ae hInt₁ hInt₂
      filter_upwards [sphereLaw_support hNpos] with y hy
      apply Real.exp_le_exp.mpr
      have ht : |overlap x y| ≤ 1 :=
        abs_le.mpr (overlap_mem_Icc_of_norm_sq hNpos x y hx hy)
      have hraw := pure_source_covariance_major_on_cap p hp β ha hq ht
      have hdim : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hbase : β^2*sourceValueTau
          (FiniteMixture.pure p hp 1 (by positivity)) 1 q (overlap x y) ≤
          b*(overlap x y)^2 := (le_abs_self _).trans hraw
      nlinarith [mul_nonneg hdim (sub_nonneg.mpr hbase)]
    _ ≤ C := hN x hx

end
end SlowEquilibration.SourcePureCapPosteriorAngularBudget
