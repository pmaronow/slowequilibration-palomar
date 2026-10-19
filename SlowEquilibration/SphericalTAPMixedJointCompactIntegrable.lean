-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmJointFubini

@[expose] public section

/-! Compact-rectangle integrability of the literal physical mixed joint
Laplace integrand. This supplies the Fubini side condition for source 12.17
independently of any asymptotic saddle estimate. -/

namespace SlowEquilibration.SphericalTAPMixedJointCompactIntegrable
noncomputable section
open Set MeasureTheory StrongFieldComplexity
open SphericalTAPMixedBandExponent SphericalTAPMixedLatitudeSmooth
open SphericalTAPMixedPhysicalChi SphericalTAPMixedPhysicalJointLaplace
open SphericalMarkedWindows ConditionedEntrance
set_option autoImplicit false
set_option linter.style.haveILetI false

theorem sourceMixedXi_joint_continuous
    (μ : FiniteMixture) (β Q e : ℝ) :
    Continuous (fun z : ℝ × ℝ => sourceMixedXi μ β Q e z.1 z.2) := by
  have hv := valueTheta_continuous μ Q
  have hr := radialTheta_continuous μ Q
  have hc := (sourceMixedVariance_smooth μ Q).continuous
  unfold sourceMixedXi sourceMixedMean
  fun_prop

theorem sourceMixedBandExponent_continuousOn_box
    (μ : FiniteMixture) (β Q e L R q b : ℝ)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1) :
    ContinuousOn (fun z : ℝ × ℝ =>
      sourceMixedBandExponent μ β Q e z.1 z.2)
      ((Icc L R) ×ˢ (Icc (q-b) (q+b))) := by
  let S := (Icc L R) ×ˢ (Icc (q-b) (q+b))
  have hg : ContinuousOn (fun z : ℝ × ℝ =>
      Real.log (1-z.2^2)) S := by
    have hbase : Continuous (fun z : ℝ × ℝ => 1-z.2^2) := by fun_prop
    apply hbase.continuousOn.log
    intro z hz
    have ha := hband hz.2
    exact (by nlinarith [ha.1,ha.2] : 0 < 1-z.2^2).ne'
  have hr : Continuous (fun z : ℝ × ℝ =>
      sourceRadialProfile μ Q e z.1) :=
    (sourceRadialProfile_continuous μ Q e).comp continuous_fst
  have hξ := sourceMixedXi_joint_continuous μ β Q e
  unfold sourceMixedBandExponent
  exact (hr.continuousOn.add hξ.continuousOn).add (hg.div_const 2)

theorem sourceMixedJointIntegrand_integrableOn_compact
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R) (hb : 0 < b)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1) :
    IntegrableOn (sourceMixedJointIntegrand d μ β Q e)
      ((Icc L R) ×ˢ (Icc (q-b) (q+b))) planeVolume := by
  let U := Icc L R
  let A := Icc (q-b) (q+b)
  let S := U ×ˢ A
  obtain ⟨cχ,Cχ,hcχ,hCχ,hχ⟩ :=
    sourceMixedChi_bounds μ (R := R) hQ hEdge
  have hcomp : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hnonempty : S.Nonempty := by
    refine ⟨((L+R)/2,q),?_⟩
    constructor
    · constructor <;> linarith
    · constructor <;> linarith
  obtain ⟨z₀,hz₀,hmax⟩ := hcomp.exists_isMaxOn hnonempty
    (sourceMixedBandExponent_continuousOn_box μ β Q e L R q b hband)
  let H := sourceMixedBandExponent μ β Q e z₀.1 z₀.2
  let W := Cχ*(1-(q+b)^2)^(-(3/2:ℝ))*Real.exp (((d+2:ℕ):ℝ)*H)
  have hq0 : 0 < q := by
    have ha := hband (show q-b ∈ A from ⟨le_refl _,by linarith⟩)
    linarith [ha.1]
  have hqb : q+b < 1 :=
    (hband (show q+b ∈ A from ⟨by linarith,le_refl _⟩)).2
  have ht : 0 < 1-(q+b)^2 := by nlinarith [hq0,hqb,hb]
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hMeas : AEStronglyMeasurable
      (sourceMixedJointIntegrand d μ β Q e) (planeVolume.restrict S) :=
    (sourceMixedJointIntegrand_measurable d μ β Q e).aestronglyMeasurable
  have hPoint (z : ℝ × ℝ) (hz : z ∈ S) :
      0 ≤ sourceMixedJointIntegrand d μ β Q e z ∧
      sourceMixedJointIntegrand d μ β Q e z ≤ W := by
    have hk : z.1 ∈ U := hz.1
    have ha : z.2 ∈ A := hz.2
    have hχz := hχ d z.1 hk
    have ha0 : 0 ≤ z.2 := (hband ha).1.le
    have ha1 : z.2 ≤ q+b := ha.2
    have hpow : (1-z.2^2)^(-(3/2:ℝ)) ≤
        (1-(q+b)^2)^(-(3/2:ℝ)) := by
      have hsq : z.2^2 ≤ (q+b)^2 := by
        have hh : 0 ≤ (q+b-z.2)*(q+b+z.2) := by
          apply mul_nonneg <;> linarith
        nlinarith
      exact Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
    have hrate : sourceMixedBandExponent μ β Q e z.1 z.2 ≤ H := hmax hz
    have hExp : Real.exp (((d+2:ℕ):ℝ)*
          sourceMixedBandExponent μ β Q e z.1 z.2) ≤
        Real.exp (((d+2:ℕ):ℝ)*H) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hrate (by positivity))
    have hw0 : 0 ≤ (1-z.2^2)^(-(3/2:ℝ)) :=
      Real.rpow_nonneg (by nlinarith [(hband ha).1,(hband ha).2]) _
    unfold sourceMixedJointIntegrand
    constructor
    · exact mul_nonneg (mul_nonneg (hcχ.trans_le hχz.1).le hw0)
        (Real.exp_pos _).le
    · dsimp [W]
      exact mul_le_mul
        (mul_le_mul hχz.2 hpow hw0 hCχ.le) hExp
          (Real.exp_pos _).le (mul_nonneg hCχ.le
            (Real.rpow_nonneg ht.le _))
  letI : IsFiniteMeasureOnCompacts planeVolume := by
    dsimp [planeVolume]
    infer_instance
  have hConst : IntegrableOn (fun _ : ℝ × ℝ => W) S planeVolume :=
    integrableOn_const hcomp.measure_ne_top
  apply hConst.mono' hMeas
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
  rw [Real.norm_of_nonneg (hPoint z hz).1]
  exact (hPoint z hz).2

end
end SlowEquilibration.SphericalTAPMixedJointCompactIntegrable
