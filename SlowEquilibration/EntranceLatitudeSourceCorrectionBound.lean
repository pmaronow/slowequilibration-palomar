-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudePosteriorMeanBound

/-! The literal source correction is controlled by the sampled H_Q
field's own tangent observable. All center quantities are its true
original seed observations on the actual regular tensor event. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open ConditionedEntrance
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sourceLatitudeCorrectionConstant (μ : FiniteMixture) (Q M : ℝ) : ℝ :=
  regressionOrderConstant μ Q*(1+M+sourceLatitudeCenterConstant μ Q)

/-- Source literal δ is bounded by N|r|^d and its own centered-model
raw tangent observable, with a fixed actual-model constant. -/
theorem actual_sourceRegressionCorrection_abs_le_observable {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) {M : ℝ} (hM : 0≤M)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈regularDisorder)
    (u x : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    {e k : ℝ} (he : |e|≤M) (hk : |k|≤M) :
    |sourceRegressionCorrection μ Q hQ hnp J u e k x|≤
      sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree+
          Real.sqrt ((n+1 : ℕ) : ℝ)*|overlap x u|^(μ.minDegree-1)*
            |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|) := by
  let r := overlap x u
  let C := sourceLatitudeCenterConstant μ Q
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let A := ((n+1 : ℕ) : ℝ)*e-field cQ J u
  let B := ((n+1 : ℕ) : ℝ)*k-jet cQ 1 u (fun _ => u) J
  let G := surfaceGradient (field cQ J) u
  have hN : (0 : ℝ)<((n+1 : ℕ) : ℝ) := by positivity
  have hs : 0<Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hN
  have hr : |r|≤1 := by
    unfold r overlap
    rw [abs_div,abs_of_pos hN]
    apply (div_le_one hN).mpr
    apply (abs_real_inner_le_norm x u).trans_eq
    rw [SphericalAging.LandscapeDerivatives.sphere_norm x hx,
      SphericalAging.LandscapeDerivatives.sphere_norm u hu,Real.mul_self_sqrt hN.le]
  have hobs := source_latitude_center_observations μ Q J hJ u hu
  have hC : 0<C := derivativeConstant_pos _
  have hmark (a b : ℝ) (ha : |a|≤M) (hb : |b|≤C*((n+1 : ℕ) : ℝ)) :
      |((n+1 : ℕ) : ℝ)*a-b|≤(M+C)*((n+1 : ℕ) : ℝ) := by
    have h : |((n+1 : ℕ) : ℝ)*a-b|≤|((n+1 : ℕ) : ℝ)*a|+|b| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (((n+1 : ℕ) : ℝ)*a) 0 b
    rw [abs_mul,abs_of_pos hN] at h
    apply (h.trans (add_le_add (mul_le_mul_of_nonneg_left ha hN.le) hb)).trans_eq
    ring
  have hA := hmark e _ he hobs.1
  have hB := hmark k _ hk hobs.2
  have ht := mixed_regression_orders μ Q hr
  have ht3 : |tangentTheta μ Q r|≤regressionOrderConstant μ Q*|r|^(μ.minDegree-1) := by
    linarith [abs_nonneg (valueThetaDerivative μ Q r),abs_nonneg (radialThetaDerivative μ Q r)]
  have hval : |valueTheta μ Q r*A+radialTheta μ Q r*B|≤
      regressionOrderConstant μ Q*|r|^μ.minDegree*((M+C)*((n+1 : ℕ) : ℝ)) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    calc
      _≤|valueTheta μ Q r| *((M+C)*((n+1 : ℕ) : ℝ))+
          |radialTheta μ Q r| *((M+C)*((n+1 : ℕ) : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
      _=(|valueTheta μ Q r|+|radialTheta μ Q r|)*((M+C)*((n+1 : ℕ) : ℝ)) := by ring
      _≤_ := mul_le_mul_of_nonneg_right ht.1 (by positivity)
  have hG : |inner ℝ G x|=Real.sqrt ((n+1 : ℕ) : ℝ)*|observable cQ J x u| := by
    unfold observable
    rw [abs_mul,abs_inv,abs_of_pos hs]
    field_simp
    rfl
  have htan : |tangentTheta μ Q r*inner ℝ G x|≤
      regressionOrderConstant μ Q*|r|^(μ.minDegree-1)*
        (Real.sqrt ((n+1 : ℕ) : ℝ)*|observable cQ J x u|) := by
    rw [abs_mul,hG]
    exact mul_le_mul_of_nonneg_right ht3 (by positivity)
  change |valueTheta μ Q r*A+radialTheta μ Q r*B-tangentTheta μ Q r*inner ℝ G x|≤_
  have hd : |valueTheta μ Q r*A+radialTheta μ Q r*B-tangentTheta μ Q r*inner ℝ G x|≤
      |valueTheta μ Q r*A+radialTheta μ Q r*B|+|tangentTheta μ Q r*inner ℝ G x| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
      (valueTheta μ Q r*A+radialTheta μ Q r*B) 0 (tangentTheta μ Q r*inner ℝ G x)
  apply (hd.trans (add_le_add hval htan)).trans
  have hc0 := (regressionOrderConstant_pos μ Q).le
  have hv0 : 0≤((n+1 : ℕ) : ℝ)*|r|^μ.minDegree := by positivity
  have hz0 : 0≤Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*|observable cQ J x u| := by positivity
  dsimp only [sourceLatitudeCorrectionConstant,r,cQ,C]
  nlinarith [mul_nonneg hc0 hv0,mul_nonneg (mul_nonneg hc0 (add_nonneg hM hC.le)) hz0]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
