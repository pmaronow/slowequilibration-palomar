-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPhysicalChi
public import SlowEquilibration.ConditionedEntranceJointJets
public import SlowEquilibration.SphericalMarkedRadialSaddle

@[expose] public section

/-! The real two-variable integral from the mixed manuscript Laplace step,
with the genuine GOE determinant prefactor and the latitude Jacobian. -/

namespace SlowEquilibration.SphericalTAPMixedPhysicalJointLaplace
noncomputable section
open Set MeasureTheory StrongFieldComplexity
open SphericalTAPMixedPlaneLaplaceUpper SphericalTAPMixedPhysicalChi
open SphericalTAPMixedShiftedPlaneGaussian
open SphericalTAPMixedBandExponent SphericalTAPMixedNearbyGaussianCenter
open SphericalTAPMixedLatitudeSmooth SphericalMarkedWindows ConditionedEntrance
set_option autoImplicit false

def sourceMixedJointIntegrand (n : ℕ) (μ : FiniteMixture)
    (β Q e : ℝ) (z : ℝ × ℝ) : ℝ :=
  sourceMixedChi n μ Q z.1 * (1-z.2^2)^(-(3/2:ℝ)) *
    Real.exp ((n+2 : ℕ)*sourceMixedBandExponent μ β Q e z.1 z.2)

theorem sourceMixedBandExponent_joint_measurable (μ : FiniteMixture)
    (β Q e : ℝ) :
    Measurable (fun z : ℝ × ℝ => sourceMixedBandExponent μ β Q e z.1 z.2) := by
  have hm : Continuous (fun z : ℝ × ℝ => sourceMixedMean μ Q e z.1 z.2) := by
    unfold sourceMixedMean
    have hv := ConditionedEntrance.valueTheta_continuous μ Q
    have hr := ConditionedEntrance.radialTheta_continuous μ Q
    fun_prop
  have hv : Continuous (fun z : ℝ × ℝ => sourceMixedVariance μ Q z.2) :=
    (sourceMixedVariance_smooth μ Q).continuous.comp continuous_snd
  have hr : Continuous (fun z : ℝ × ℝ => sourceRadialProfile μ Q e z.1) :=
    (sourceRadialProfile_continuous μ Q e).comp continuous_fst
  unfold sourceMixedBandExponent sourceMixedXi
  fun_prop

theorem sourceMixedJointIntegrand_measurable (n : ℕ) (μ : FiniteMixture)
    (β Q e : ℝ) : Measurable (sourceMixedJointIntegrand n μ β Q e) := by
  have hχ : Measurable (fun z : ℝ × ℝ => sourceMixedChi n μ Q z.1) :=
    (sourceMixedChi_measurable n μ Q).comp measurable_fst
  have hg := sourceMixedBandExponent_joint_measurable μ β Q e
  unfold sourceMixedJointIntegrand
  fun_prop

/-- The exact printed weighted `U × I_b` integral has two Gaussian widths.
The exponent height `H` and negative curvature `c` are explicit premises,
so this lemma can be reused for either a moving saddle or a fixed contact. -/
theorem sourceMixedJointIntegral_upper_of_envelope
    (n : ℕ) (μ : FiniteMixture) {β Q e L R K q b c Cχ H : ℝ}
    (hχ : ∀ k ∈ Icc L R, 0 ≤ sourceMixedChi n μ Q k ∧
      sourceMixedChi n μ Q k ≤ Cχ)
    (hCχ : 0 ≤ Cχ) (hc : 0 < c) (hb : 0 < b)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0 : ℝ) 1)
    (henv : ∀ k ∈ Icc L R, ∀ a ∈ Icc (q-b) (q+b),
      sourceMixedBandExponent μ β Q e k a ≤
        H-c*((k-K)^2+(a-q)^2)) :
    let U := Icc L R
    let I := Icc (q-b) (q+b)
    (∫ z in U ×ˢ I, sourceMixedJointIntegrand n μ β Q e z ∂planeVolume) ≤
      (Cχ*(1-(q+b)^2)^(-(3/2:ℝ))*Real.pi/c)*
        Real.exp ((n+2 : ℕ)*H)/(n+2 : ℕ) := by
  dsimp only
  let U := Icc L R
  let I := Icc (q-b) (q+b)
  let S := U ×ˢ I
  let N : ℝ := (n+2 : ℕ)
  let W₀ := (1-(q+b)^2)^(-(3/2:ℝ))
  let W := Cχ*W₀
  have hq0 : 0 < q := by
    have hh : q-b ∈ I := ⟨le_refl _, by linarith⟩
    have hp := (hband hh).1
    linarith
  have hqb : q+b < 1 := by
    have hh : q+b ∈ I := ⟨by linarith,le_refl _⟩
    exact (hband hh).2
  have hs0 : 0 < 1-(q+b)^2 := by nlinarith [hq0,hb,hqb]
  have hW₀ : 0 < W₀ := Real.rpow_pos_of_pos hs0 _
  have hW : 0 ≤ W := mul_nonneg hCχ hW₀.le
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hN : 0 < N := by dsimp [N]; positivity
  have hfm : AEStronglyMeasurable (sourceMixedJointIntegrand n μ β Q e)
      (planeVolume.restrict S) :=
    (sourceMixedJointIntegrand_measurable n μ β Q e).aestronglyMeasurable
  have hweight (a : ℝ) (ha : a ∈ I) :
      (1-a^2)^(-(3/2:ℝ)) ≤ W₀ := by
    have ha0 : 0 ≤ a := by have hh := (hband ha).1; linarith
    have ha1 : a ≤ q+b := ha.2
    have hsq : a^2 ≤ (q+b)^2 := by
      have hh : 0 ≤ ((q+b)-a)*((q+b)+a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact Real.rpow_le_rpow_of_nonpos hs0 (by linarith) (by norm_num)
  have hpoint (z : ℝ × ℝ) (hz : z ∈ S) :
      sourceMixedJointIntegrand n μ β Q e z ≤
        W*Real.exp (N*H)*shiftedGaussianPlane (c*N) K q z := by
    have hk : z.1 ∈ U := hz.1
    have ha : z.2 ∈ I := hz.2
    have hχk := hχ z.1 hk
    have hw0 : 0 ≤ (1-z.2^2)^(-(3/2:ℝ)) := Real.rpow_nonneg (by
      have hh := hband ha
      nlinarith [hh.1,hh.2]) _
    have hχw : sourceMixedChi n μ Q z.1*(1-z.2^2)^(-(3/2:ℝ)) ≤ W := by
      dsimp [W]
      exact mul_le_mul hχk.2 (hweight z.2 ha) hw0 hCχ
    have hExp : Real.exp (N*sourceMixedBandExponent μ β Q e z.1 z.2) ≤
        Real.exp (N*H)*shiftedGaussianPlane (c*N) K q z := by
      unfold shiftedGaussianPlane
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := henv z.1 hk z.2 ha
      nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hh)]
    unfold sourceMixedJointIntegrand
    change sourceMixedChi n μ Q z.1*(1-z.2^2)^(-(3/2:ℝ))*
      Real.exp (N*sourceMixedBandExponent μ β Q e z.1 z.2) ≤ _
    apply (mul_le_mul_of_nonneg_right hχw (Real.exp_pos _).le).trans
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hExp hW)
  have hpos (z : ℝ × ℝ) (hz : z ∈ S) :
      0 ≤ sourceMixedJointIntegrand n μ β Q e z := by
    unfold sourceMixedJointIntegrand
    exact mul_nonneg (mul_nonneg (hχ z.1 hz.1).1
      (Real.rpow_nonneg (by nlinarith [(hband hz.2).1,(hband hz.2).2]) _))
        (Real.exp_pos _).le
  have hupper := plane_weighted_laplace_upper hS hfm hN hc hW hpos hpoint
  simpa only [S,U,I,W,W₀,N] using hupper

end
end SlowEquilibration.SphericalTAPMixedPhysicalJointLaplace
