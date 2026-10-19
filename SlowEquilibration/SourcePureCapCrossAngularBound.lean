-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapMixedLatitudeOverlap
public import SlowEquilibration.SourcePureCapPosteriorCrossBudget
public import SlowEquilibration.SourcePureCapPosteriorAngularBudget
public import SlowEquilibration.SphericalSubcriticalOverlapMoment

/-! Uniform transverse two-latitude covariance integral at the exact
physical ambient dimension N=n+1. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapCrossAngularBound
noncomputable section
open Set Filter MeasureTheory SphericalForm
open SphericalModel PureStationarity
open SourcePureCapPosteriorCrossBudget
open SourcePureCapPosteriorAngularBudget
open SourcePureCapPosteriorCrossKernel
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_source_cross_angular_exponential_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (x : Vector n), ‖x‖^2 = (n : ℝ) →
      ∀ q₁ ∈ Ico a 1, ∀ q₂ ∈ Ico a 1,
      (∫ y : Vector n,
        Real.exp (((n+1 : ℕ) : ℝ)*β^2*
          sourceValueTauCross (FiniteMixture.pure p hp 1 (by positivity))
            1 q₁ q₂
            (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*overlap x y))
          ∂sphereLaw n) ≤ C := by
  let κ := pureResidualCoefficient p β a
  let b := (κ+1/2)/2
  have hκ0 : 0 ≤ κ := pureResidualCoefficient_nonneg p hp β a
  have hgap : 0 < b-κ := by dsimp [b]; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbsub : b < 1/2 := by dsimp [b]; linarith
  obtain ⟨C,hC,hbound⟩ := sphere_overlap_exp_square_eventually_bounded hb0 hbsub
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (κ/(b-κ))
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (n₀+1)] with n hbound hn
  intro x hx q₁ hq₁ q₂ hq₂
  have hnpos : 1 ≤ n := by omega
  have hnreal : (n₀ : ℝ) < (n : ℝ) := by exact_mod_cast (show n₀<n by omega)
  have hratio : ((n+1 : ℕ) : ℝ)*κ ≤ b*(n : ℝ) := by
    have hlt : κ/(b-κ) < (n : ℝ) := lt_trans hn₀ hnreal
    have hlt' := (div_lt_iff₀ hgap).mp hlt
    push_cast
    nlinarith
  have hcont₁ : Continuous (fun y : Vector n =>
      Real.exp (((n+1 : ℕ) : ℝ)*β^2*
        sourceValueTauCross (FiniteMixture.pure p hp 1 (by positivity))
          1 q₁ q₂
          (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*overlap x y))) := by
    simp only [sourceValueTauCross_pure p hp 1 (by positivity)
      (by norm_num : (0 : ℝ) < 1)]
    unfold overlap
    fun_prop
  have hcont₂ : Continuous (fun y : Vector n =>
      Real.exp (b*(n : ℝ)*(overlap x y)^2)) := by
    unfold overlap
    fun_prop
  have hInt₁ := integrable_sphereSupported_continuous (sphereLaw n)
    (sphereLaw_support hnpos) hcont₁
  have hInt₂ := integrable_sphereSupported_continuous (sphereLaw n)
    (sphereLaw_support hnpos) hcont₂
  calc
    _ ≤ ∫ y : Vector n, Real.exp (b*(n : ℝ)*(overlap x y)^2) ∂sphereLaw n := by
      apply integral_mono_ae hInt₁ hInt₂
      filter_upwards [sphereLaw_support hnpos] with y hy
      apply Real.exp_le_exp.mpr
      have ht : |overlap x y| ≤ 1 :=
        abs_le.mpr (overlap_mem_Icc_of_norm_sq hnpos x y hx hy)
      have hcov := pure_source_cross_covariance_major_on_cap p hp β ha hq₁ hq₂ ht
      have hbase : β^2*sourceValueTauCross
          (FiniteMixture.pure p hp 1 (by positivity)) 1 q₁ q₂
            (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*overlap x y) ≤
          κ*(overlap x y)^2 := (le_abs_self _).trans hcov
      have hsq : 0 ≤ (overlap x y)^2 := sq_nonneg _
      have hdim : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hdim (sub_nonneg.mpr hbase),
        mul_nonneg hsq (sub_nonneg.mpr hratio)]
    _ ≤ C := hbound x hx

end
end SlowEquilibration.SourcePureCapCrossAngularBound
