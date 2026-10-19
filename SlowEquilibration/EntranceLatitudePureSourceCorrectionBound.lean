-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceCorrectionBound
public import SlowEquilibration.SphericalOriginalPureSourceCorrection
public import SlowEquilibration.CSPureModels

/-! The proper pure correction is bounded from its genuine value and
zero-gradient conditioning formula. Its scalar coefficient is controlled
without using a singular two-score inverse. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open ConditionedEntrance SphericalCriticalLatitude
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The true pure value scale is bounded by the fixed polynomial-order
constant through its nonsingular tangent coefficient. -/
theorem pure_source_inverse_scale_le (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    {Q : ℝ} (hQ : 0<Q) :
    ((Real.sqrt Q)^p)⁻¹≤regressionOrderConstant (FiniteMixture.pure p hp c hc) Q := by
  have ht := mixed_regression_orders (FiniteMixture.pure p hp c hc) Q (r := 1) (by norm_num)
  rw [pure_original_tangent_coefficient p hp c hc hQ] at ht
  simp only [one_pow,abs_one,mul_one] at ht
  have hs : 0≤((Real.sqrt Q)^p)⁻¹ := by positivity
  rw [abs_of_nonneg hs] at ht
  linarith [abs_nonneg (valueThetaDerivative (FiniteMixture.pure p hp c hc) Q 1),
    abs_nonneg (radialThetaDerivative (FiniteMixture.pure p hp c hc) Q 1)]

/-- Literal proper pure δ is controlled by its actual H_Q tangent
observable and the same fixed-model source coefficient envelope. -/
theorem actual_pureSourceRegressionCorrection_abs_le_observable {n : ℕ}
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) {Q : ℝ} (hQ : 0<Q)
    {M : ℝ} (hM : 0≤M) (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J∈regularDisorder) (u x : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (_hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    {e : ℝ} (he : |e|≤M) :
    let μ := FiniteMixture.pure p hp c hc
    |pureSourceRegressionCorrection p hp c hc Q J u e x|≤
      sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree+
          Real.sqrt ((n+1 : ℕ) : ℝ)*|overlap x u|^(μ.minDegree-1)*
            |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let C := sourceLatitudeCenterConstant μ Q
  let L := ((Real.sqrt Q)^p)⁻¹
  let r := overlap x u
  let A := ((n+1 : ℕ) : ℝ)*e-field cQ J u
  let G := surfaceGradient (field cQ J) u
  have hN : (0 : ℝ)<((n+1 : ℕ) : ℝ) := by positivity
  have hs : 0<Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hN
  have hL : 0≤L := by dsimp [L];positivity
  have hLb := pure_source_inverse_scale_le p hp c hc hQ
  have hobs := source_latitude_center_observations μ Q J hJ u hu
  have hC : 0<C := derivativeConstant_pos _
  have hA : |A|≤(M+C)*((n+1 : ℕ) : ℝ) := by
    have h : |A|≤|((n+1 : ℕ) : ℝ)*e|+|field cQ J u| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (((n+1 : ℕ) : ℝ)*e) 0 (field cQ J u)
    rw [abs_mul,abs_of_pos hN] at h
    apply (h.trans (add_le_add (mul_le_mul_of_nonneg_left he hN.le) hobs.1)).trans_eq
    ring
  have hG : |inner ℝ G x|=Real.sqrt ((n+1 : ℕ) : ℝ)*|observable cQ J x u| := by
    unfold observable
    rw [abs_mul,abs_inv,abs_of_pos hs]
    field_simp
    rfl
  have hδ : |L*(A*r^p-r^(p-1)*inner ℝ G x)|≤
      L*((M+C)*((n+1 : ℕ) : ℝ)*|r|^p+
        |r|^(p-1)*(Real.sqrt ((n+1 : ℕ) : ℝ)*|observable cQ J x u|)) := by
    rw [abs_mul,abs_of_nonneg hL]
    apply mul_le_mul_of_nonneg_left _ hL
    have hh : |A*r^p-r^(p-1)*inner ℝ G x|≤|A*r^p|+|r^(p-1)*inner ℝ G x| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (A*r^p) 0 (r^(p-1)*inner ℝ G x)
    apply hh.trans
    rw [abs_mul,abs_mul,abs_pow,abs_pow,hG]
    exact add_le_add (mul_le_mul_of_nonneg_right hA (by positivity)) le_rfl
  change |L*(A*r^p-r^(p-1)*inner ℝ G x)|≤_
  apply hδ.trans
  rw [(CSPureModels.pure_degrees p hp c hc).1]
  have hc0 := (regressionOrderConstant_pos μ Q).le
  have hv0 : 0≤((n+1 : ℕ) : ℝ)*|r|^p := by positivity
  have hz0 : 0≤Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(p-1)*|observable cQ J x u| := by positivity
  have hLD : L≤regressionOrderConstant μ Q := hLb
  have hsmall := mul_le_mul_of_nonneg_right hLD (by positivity :
    0≤(M+C)*((n+1 : ℕ) : ℝ)*|r|^p+|r|^(p-1)*(Real.sqrt ((n+1 : ℕ) : ℝ)*|observable cQ J x u|))
  apply hsmall.trans
  dsimp only [sourceLatitudeCorrectionConstant,r,cQ,C]
  nlinarith [mul_nonneg hc0 hv0,mul_nonneg (mul_nonneg hc0 (add_nonneg hM hC.le)) hz0]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
