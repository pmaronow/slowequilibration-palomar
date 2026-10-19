-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPalmBandLower

@[expose] public section

/-! Proper value-only pure conditioning: the radial mark is the deterministic
Euler value `p e`, and the source band and Palm determinant use that same law. -/

namespace SlowEquilibration.SphericalTAPCriticalPurePalmBandLower
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open PairConditionalDeterminantMoments ConditionedDeterminantMoments
open SphericalTAPCriticalBand SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalPalmHolder SphericalTAPCriticalPalmAssembly
open SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Finite-N source 12.20 Palm lower-tail inequality for the proper pure
value-conditioned law; the normalized transverse residual is literal. -/
theorem pure_sourcePalm_band_lower_tail
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q M r β g Z : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hβ : 0 ≤ β) (hg : 0 < g)
    (I : Set ℝ) (hImeas : MeasurableSet I)
    (hI : I ⊆ Icc (-r) r) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ C_lat C_det : ℝ, 0 < C_lat ∧ 0 < C_det ∧
      ∀ (d : ℕ), 1 ≤ d →
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
      ∀ a : ℝ, |a| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*a → (p:ℝ)*a ≤ Z →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((d+2:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((d+2:ℕ):ℝ))) ⊆ I →
      ∀ (mN δ : ℝ), 0 < δ →
      let ν := pureLaw p hp alpha halpha Q u hu a
      let D := intrinsicDet μ Q u
      let scale := sourceCriticalBandScale (d+1) μ hQ β mN *
        Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
      let c := 2 * Real.exp (-(β*C_lat+2/(1-r^2)^2)/2)
      (∫ J in {J | partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) < δ*scale}, D J ∂ν) /
        (∫ J, D J ∂ν) ≤
      Real.sqrt C_det *
        (Real.sqrt ((Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((d+2:ℕ):ℝ)/2)) +
        Real.sqrt (ν.real
          {J | sourceRadiusCriticalResidualNormalizedPartition (d+1) μ hQ u
            (latitudeFrameAt u) β a J < δ/c})) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  obtain ⟨K,C_lat,hK,hC_lat,hgood⟩ :=
    valueConditioned_sourceBand_residual_comparison μ hQ hM
      hr0 hr1 hβ I hI
  obtain ⟨C_det,hC_det,hholder⟩ :=
    pure_critical_determinant_event_bound p hp alpha halpha hQ.1 hg
      (Z := Z)
  obtain ⟨C_mom,hC_mom,hmom⟩ :=
    pure_conditioned_determinant_moments p hp alpha halpha hQ.1 hg
      (Z := Z) (r := 2) (by norm_num)
  refine ⟨C_lat,C_det,hC_lat,hC_det,?_⟩
  intro d hd u hu a ha hag haZ hband mN δ hδ
  let ν := pureLaw p hp alpha halpha Q u hu a
  let D := intrinsicDet μ Q u
  let scale := sourceCriticalBandScale (d+1) μ hQ β mN *
    Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
  let c := 2 * Real.exp (-(β*C_lat+2/(1-r^2)^2)/2)
  have hmark : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*a := hag
  have hscale : 0 < scale := mul_pos
    (sourceCriticalBandScale_pos (d+1) (by omega) μ hQ β mN)
      (Real.exp_pos _)
  have hc : 0 < c := mul_pos (by norm_num) (Real.exp_pos _)
  have hP : IsProbabilityMeasure ν := by
    dsimp only [ν]
    unfold pureLaw
    infer_instance
  let : IsProbabilityMeasure ν := hP
  have hLaw : ν = valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu a := rfl
  obtain ⟨hbadmeas,hbadtail,hcomparison⟩ :=
    hgood (d+1) (by omega) u hu a ha hband mN
  have hbadtail' : ν.real
      (sourcePosteriorOrderedRegularity
        (N := d+2) (P := μ.maxDegree) K)ᶜ ≤
      (Fintype.card (Degree μ.maxDegree):ℝ) *
        Real.exp (-((d+2:ℕ):ℝ)/2) := by
    simpa only [hLaw] using hbadtail
  have hcomp : ∀ J ∉
      (sourcePosteriorOrderedRegularity
        (N := d+2) (P := μ.maxDegree) K)ᶜ,
      c * scale *
        sourceRadiusCriticalResidualNormalizedPartition (d+1) μ hQ u
          (latitudeFrameAt u) β a J ≤
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I) := by
    intro J hJ
    have hgJ : J ∈ sourcePosteriorOrderedRegularity
        (N := d+2) (P := μ.maxDegree) K := by simpa using hJ
    simpa only [c,scale,mul_assoc] using hcomparison J hgJ
  have hMoms := hmom d u hu a hmark haZ
  have hBandMeas : Measurable (fun J : Disorder (d+2) μ.maxDegree =>
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I)) :=
    sourceBandPartition_measurable (d+1) μ u I hImeas β
  have hResMeas : Measurable
      (sourceRadiusCriticalResidualNormalizedPartition (d+1) μ hQ u
        (latitudeFrameAt u) β a) :=
    sourceRadiusCriticalResidualNormalizedPartition_measurable
      (d+1) (by omega) μ hQ u (latitudeFrameAt u) β a
  have hHolder : ∀ A : Set (Disorder (d+2) μ.maxDegree),
      MeasurableSet A →
      (∫ J in A, D J ∂ν) ≤ Real.sqrt C_det *
        Real.sqrt (ν.real A) * (∫ J, D J ∂ν) := by
    intro A hA
    exact hholder d u hu a hmark haZ A hA
  have hPalm := palm_band_tail_le_regular_and_residual ν D
    (fun J => partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I))
    (sourceRadiusCriticalResidualNormalizedPartition (d+1) μ hQ u
      (latitudeFrameAt u) β a)
    (sourcePosteriorOrderedRegularity
      (N := d+2) (P := μ.maxDegree) K)ᶜ
    hMoms.1 (fun _ => abs_nonneg _) hMoms.2.2.1
    hbadmeas.compl hBandMeas hResMeas hC_det.le hc hscale hδ
    hcomp hHolder
  dsimp only [ν,D,scale,c] at hPalm ⊢
  exact hPalm.trans (mul_le_mul_of_nonneg_left
    (add_le_add (Real.sqrt_le_sqrt hbadtail') le_rfl)
      (Real.sqrt_nonneg _))

/-- The proper pure value-only fixed-mark Palm lower tail, uniformly over
bounded compatible energy marks and above-edge deterministic Euler shifts. -/
theorem pure_sourcePalm_band_lower_tight
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    {M r g Z : ℝ} (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hg : 0 < g)
    (I : Set ℝ) (hImeas : MeasurableSet I)
    (hI : I ⊆ Icc (-r) r) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ d : ℕ in atTop,
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
      ∀ a : ℝ, |a| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*a → (p:ℝ)*a ≤ Z →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((d+2:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((d+2:ℕ):ℝ))) ⊆ I →
      ∀ mN : ℝ,
      let ν := pureLaw p hp alpha halpha Q u hu a
      let D := intrinsicDet μ Q u
      let scale := sourceCriticalBandScale (d+1) μ h.overlap_range β mN *
        Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
      (∫ J in {J | partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) < δ*scale}, D J ∂ν) /
        (∫ J, D J ∂ν) ≤ ε := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  obtain ⟨C_lat,C_det,hC_lat,hC_det,hFinite⟩ :=
    pure_sourcePalm_band_lower_tail p hp alpha halpha h.overlap_range
      hM hr0 hr1 h.beta_pos.le hg I hImeas hI
  intro ε hε
  let η : ℝ := (ε/(4*Real.sqrt C_det))^2
  have hη : 0 < η := sq_pos_of_pos
    (div_pos hε (mul_pos (by norm_num) (Real.sqrt_pos.mpr hC_det)))
  obtain ⟨t,ht,hTail⟩ :=
    sourceRadius_value_critical_partition_lower_tail μ h η hη
  let c : ℝ := 2*Real.exp (-(β*C_lat+2/(1-r^2)^2)/2)
  have hc : 0 < c := mul_pos (by norm_num) (Real.exp_pos _)
  let δ : ℝ := c*t
  have hδ : 0 < δ := mul_pos hc ht
  refine ⟨δ,hδ,?_⟩
  have hdim : Tendsto (fun d : ℕ => ((d+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun d : ℕ =>
      Real.exp (-((d+2:ℕ):ℝ)/2)) atTop (𝓝 (0:ℝ)) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hdim.const_mul_atTop (by norm_num : (0:ℝ)<1/2)) using 1
    ext d
    simp only [Function.comp_apply]
    ring_nf
  have hRate : Tendsto (fun d : ℕ =>
      (Fintype.card (Degree μ.maxDegree):ℝ)*
        Real.exp (-((d+2:ℕ):ℝ)/2)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using
      hExp.const_mul (Fintype.card (Degree μ.maxDegree):ℝ)
  have hBad : Tendsto (fun d : ℕ =>
      Real.sqrt C_det * Real.sqrt
        ((Fintype.card (Degree μ.maxDegree):ℝ)*
          Real.exp (-((d+2:ℕ):ℝ)/2))) atTop (𝓝 (0:ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero] using hRate.sqrt.const_mul (Real.sqrt C_det)
  have hsmall := hBad.eventually (gt_mem_nhds (half_pos hε))
  have hTail' := (tendsto_add_atTop_nat 1).eventually hTail
  filter_upwards [hTail',hsmall,eventually_ge_atTop (1:ℕ)]
    with d hres hbad hd
  intro u hu a ha hag haZ hband mN
  let ν := pureLaw p hp alpha halpha Q u hu a
  let D := intrinsicDet μ Q u
  let scale := sourceCriticalBandScale (d+1) μ h.overlap_range β mN *
    Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
  have hresBound := hres u hu (latitudeFrameAt u)
    (latitudeFrameAt_orthogonal u hu) a
  have hLaw : ν = valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu a := rfl
  have hresBound' : ν.real
      {J | sourceRadiusCriticalResidualNormalizedPartition (d+1) μ
        h.overlap_range u (latitudeFrameAt u) β a J < t} ≤ η := by
    simpa only [ν,hLaw] using hresBound
  have hdc : δ/c=t := by
    dsimp only [δ]
    exact mul_div_cancel_left₀ t hc.ne'
  have hPalm := hFinite d (by omega) u hu a ha hag haZ hband
    mN δ hδ
  dsimp only at hPalm ⊢
  rw [← hdc] at hresBound'
  have hresSqrt : Real.sqrt (ν.real
      {J | sourceRadiusCriticalResidualNormalizedPartition (d+1) μ
        h.overlap_range u (latitudeFrameAt u) β a J < δ/c}) ≤
      Real.sqrt η := Real.sqrt_le_sqrt hresBound'
  have hsqrtη : Real.sqrt η = ε/(4*Real.sqrt C_det) := by
    dsimp only [η]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos]
    exact div_pos hε (mul_pos (by norm_num) (Real.sqrt_pos.mpr hC_det))
  have hsmallη : Real.sqrt C_det * Real.sqrt η = ε/4 := by
    rw [hsqrtη]
    field_simp [Real.sqrt_ne_zero'.mpr hC_det]
  have hBound := hPalm.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hresSqrt) (Real.sqrt_nonneg _))
  have hbad' : Real.sqrt C_det *
      Real.sqrt ((Fintype.card (Degree μ.maxDegree):ℝ)*
        Real.exp (-((d+2:ℕ):ℝ)/2)) < ε/2 := hbad
  calc
    _ ≤ Real.sqrt C_det *
        (Real.sqrt ((Fintype.card (Degree μ.maxDegree):ℝ)*
          Real.exp (-((d+2:ℕ):ℝ)/2)) + Real.sqrt η) := hBound
    _ ≤ ε := by nlinarith [hsmallη, hbad']

end
end SlowEquilibration.SphericalTAPCriticalPurePalmBandLower
