-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapSourceRatios

/-! The source `r_L` clause: every centered near-ground critical energy has
a uniformly positive conditional microscopic-window mass. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapSourceLower
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate
open SphericalPureCapSourceRatios SourceGaussianWindowFraction
open SourceUniformScalarRatio SourceGaussianLaplaceRatio
open SphericalPureCapIntegralDecomposition PureStationarity SphericalModel
open SphericalPureCapSourceScalars
open scoped Topology
set_option autoImplicit false

private theorem sourceCapMean_nonneg
    (p n : ℕ) (β ep cp a t : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ sourceCapMean p β ep cp a n t := by
  unfold sourceCapMean
  apply mul_nonneg ENNReal.toReal_nonneg
  apply intervalIntegral.integral_nonneg ha1
  intro z hz
  have hz' : z ∈ Icc a 1 := by simpa only [uIcc_of_le ha1] using hz
  have hbase : 0 ≤ 1-z^2 := by nlinarith [ha,hz'.1,hz'.2]
  unfold rawDensity
  exact mul_nonneg (Real.rpow_nonneg hbase _) (Real.exp_pos _).le

/-- The printed source positive lower bound on the actual raw conditional
means. The explicit choice is half the least Gaussian limit over `|t|≤L`. -/
theorem sourcePure_cap_window_lower_uniform
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (L : ℝ) (hL : 0 ≤ L) :
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a κ r : ℝ, 1/Real.sqrt 2 < a ∧ a < q ∧
      0 < κ ∧ κ = SphericalPureLaplaceUniformLogCurvature.purePrintedKStar p hp β Q ∧
      0 < r ∧
      r = Real.exp (-β*L*q^p)*gaussianWindowFraction κ 1/2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (-L) L,
        r*sourceCapMean p β ep cp a n 0 ≤
          sourceWindowMean p β ep cp q 1 n t := by
  dsimp only
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hRatios⟩ :=
    sourcePure_cap_gaussian_ratios_uniform p hp h L hL
  have haq : a < Real.sqrt Q := by linarith
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let q := Real.sqrt Q
  let Γ := gaussianWindowFraction κ 1
  let c := Real.exp (-β*L*q^p)*Γ
  let r := c/2
  have hΓ : 0 < Γ := gaussianWindowFraction_pos hκ (by norm_num)
  have hc : 0 < c := mul_pos (Real.exp_pos _) hΓ
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨a,κ,r,ha,haq,hκ,hκEq,hr,rfl,?_⟩
  have hzero : (0:ℝ) ∈ Icc (-L) L := ⟨by linarith,by linarith⟩
  obtain ⟨hTr,hWr,_⟩ := hRatios 1 (by norm_num)
  have hAdiv : Tendsto
      (fun n => sourceCapMean p β ep cp a n 0 /
        sourceCapMean p β ep cp a n 0) atTop (𝓝 1) := by
    simpa only [mul_zero,zero_mul,Real.exp_zero] using hTr.tendsto_at hzero
  have hAdivPos : ∀ᶠ n : ℕ in atTop,
      1/2 < sourceCapMean p β ep cp a n 0 /
        sourceCapMean p β ep cp a n 0 :=
    hAdiv.eventually (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))
  have hApos : ∀ᶠ n : ℕ in atTop,
      0 < sourceCapMean p β ep cp a n 0 := by
    filter_upwards [hAdivPos] with n hn
    have ha0 : 0 ≤ a := (by positivity : 0 < 1/Real.sqrt 2).trans ha |>.le
    have ha1 : a ≤ 1 := by linarith
    have hnonneg := sourceCapMean_nonneg p n β ep cp a 0 ha0 ha1
    have hne : sourceCapMean p β ep cp a n 0 ≠ 0 := by
      intro heq
      simp [heq] at hn
      linarith
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hcoef : 0 ≤ β*q^p :=
    mul_nonneg h.beta_pos.le (pow_nonneg (Real.sqrt_nonneg Q) _)
  have hlimitLower : ∀ t ∈ Icc (-L) L,
      c ≤ Real.exp (β*t*q^p)*gaussianWindowFraction κ 1 := by
    intro t ht
    have hmul := mul_le_mul_of_nonneg_left ht.1 hcoef
    have hexp : Real.exp (-β*L*q^p) ≤ Real.exp (β*t*q^p) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact mul_le_mul_of_nonneg_right hexp hΓ.le
  have hWrLower := eventually_uniform_lower_half hWr hc hlimitLower
  filter_upwards [hApos,hWrLower] with n hnA hnW t ht
  have hratio := hnW t ht
  change r ≤ sourceWindowMean p β ep cp q 1 n t /
      sourceCapMean p β ep cp a n 0 at hratio
  exact (le_div_iff₀ hnA).mp hratio

end
end SlowEquilibration.SphericalPureCapSourceLower
