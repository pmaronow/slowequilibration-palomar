-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureFixedCapEstimates
public import SlowEquilibration.SourcePureCenteredGlobalMaximumTail
public import SlowEquilibration.SphericalPureCenterFieldScale

/-! The original amplitude-one pure maximum at the source's exact `M_N`.
Pathwise homogeneity transfers the proved center-field tail; no tightness
assumption is added to the microscopic capture assembly. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCaptureFixedCapEstimates
noncomputable section
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate PureStationarity
open SphericalPureCapSourceScalars SphericalPureCenterFieldScale
open TwoAtomStationarity
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_sourceSphereMaximum_eq_original_scale
    (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {Q : ℝ} (hQ : 0 < Q) (d : ℕ)
    (J : Disorder (d+2) (FiniteMixture.pure p hp α hα).maxDegree) :
    sourceSphereMaximum d (FiniteMixture.pure p hp α hα) Q J =
      (Real.sqrt Q)^p*sourceSphereMaximum d (FiniteMixture.pure p hp α hα) 1 J := by
  let μ := FiniteMixture.pure p hp α hα
  have hs : 0 < (Real.sqrt Q)^p := pow_pos (Real.sqrt_pos.mpr hQ) _
  have hc : centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
    funext k
    simp [centerCoefficients]
  obtain ⟨u,hu,_,hmaxu,hequ⟩ := sourceSphereMaximum_attained d μ Q J
  obtain ⟨v,hv,_,hmaxv,heqv⟩ := sourceSphereMaximum_attained d μ 1 J
  rw [hc] at hmaxv heqv
  have hscale (z : Vector (d+2)) :=
    pure_center_field_eq_original_scale p hp α hα hQ.le (d+2) J z
  rw [hequ,heqv,hscale]
  apply le_antisymm
  · exact mul_le_mul_of_nonneg_left (hmaxv hu) hs.le
  · have hh : field (centerCoefficients (mixtureCoefficients μ) Q) J v ≤
        field (centerCoefficients (mixtureCoefficients μ) Q) J u := hmaxu hv
    dsimp only [μ] at hh
    rw [hscale,hscale] at hh
    exact hh

/-- The actual original maximum failure probability needed by the cap
cover comparison, with a strict failure event. -/
def pureSourceMaximumFailure (p : ℕ) (hp : 4 ≤ p) (L : ℝ) (d : ℕ) : ℝ :=
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  (disorderLaw (d+2) μ.maxDegree).real
    {J | pureSourceCenter p hp d+L < sourceSphereMaximum d μ 1 J}

/-- Exponential upper tightness of the original pure maximum about the
exact manuscript center. The constant is uniform in every later L. -/
theorem pure_original_source_maximum_upper
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ,
      Filter.limsup (pureSourceMaximumFailure p hp L) atTop ≤
        C*Real.exp (-pureIntensityConstant p (by omega)*L) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let s := (Real.sqrt Q)^p
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let m (d : ℕ) := s*pureSourceCenter p hp d
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) _
  obtain ⟨hE,hc⟩ := sourcePure_certificate_scalar_coordinates p hp h
  have hm (d : ℕ) : m d = (d+2:ℕ)*markE μ β x Q-
      Real.log (d+2:ℕ)/(2*(β*x)) := by
    rw [hE]
    dsimp [m,pureSourceCenter]
    rw [← hc]
    dsimp [s]
    field_simp [h.beta_pos.ne',h.weight_range.1.ne',
      (pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p).ne']
  obtain ⟨C,hC,hUpper⟩ := sourcePure_centered_global_maximum_limsup
    p (by omega) 1 (by positivity) h m (M := 1) (by norm_num)
      (.of_forall fun d => by
        change |m d-((d+2:ℕ)*markE μ β x Q-
          Real.log (d+2:ℕ)/(2*(β*x)))| ≤ 1
        rw [hm]
        norm_num)
  refine ⟨C,hC,?_⟩
  intro L
  let P (d : ℕ) := (disorderLaw (d+2) μ.maxDegree).real
    {J | pureSourceCenter p hp d+L ≤ sourceSphereMaximum d μ 1 J}
  have hEvent (d : ℕ) :
      {J : Disorder (d+2) μ.maxDegree | m d+s*L ≤ sourceSphereMaximum d μ Q J} =
        {J | pureSourceCenter p hp d+L ≤ sourceSphereMaximum d μ 1 J} := by
    ext J
    simp only [Set.mem_ofPred_eq]
    dsimp only [μ]
    rw [pure_sourceSphereMaximum_eq_original_scale p (by omega) 1
      (by positivity) h.overlap_range.1 d J]
    change s*pureSourceCenter p hp d+s*L ≤ s*sourceSphereMaximum d μ 1 J ↔ _
    rw [←mul_add,mul_le_mul_iff_right₀ hs]
  have hexp : -(β*x)*(s*L) = -cp*L := by
    have hh : β*x*s=cp := hc
    calc
      -(β*x)*(s*L) = -(β*x*s)*L := by ring
      _ = -cp*L := by rw [hh]
  have hP : Filter.limsup P atTop ≤ C*Real.exp (-cp*L) := by
    have hh := hUpper (s*L)
    change Filter.limsup (fun d => (disorderLaw (d+2) μ.maxDegree).real
      {J | m d+s*L ≤ sourceSphereMaximum d μ Q J}) atTop ≤
        C*Real.exp (-(β*x)*(s*L)) at hh
    simpa only [P,hEvent,hexp] using hh
  have hCob : IsCoboundedUnder (· ≤ ·) atTop (pureSourceMaximumFailure p hp L) :=
    isCoboundedUnder_le_of_le atTop (fun _ => measureReal_nonneg)
  have hBdd : IsBoundedUnder (· ≤ ·) atTop P :=
    isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩
  have hpoint : ∀ᶠ d : ℕ in atTop, pureSourceMaximumFailure p hp L d ≤ P d :=
    .of_forall fun d => by
      change (disorderLaw (d+2) μ.maxDegree).real
        {J | pureSourceCenter p hp d+L < sourceSphereMaximum d μ 1 J} ≤
          (disorderLaw (d+2) μ.maxDegree).real
            {J | pureSourceCenter p hp d+L ≤ sourceSphereMaximum d μ 1 J}
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro J hJ
      change pureSourceCenter p hp d+L < sourceSphereMaximum d μ 1 J at hJ
      change pureSourceCenter p hp d+L ≤ sourceSphereMaximum d μ 1 J
      exact hJ.le
  exact (limsup_le_limsup hpoint hCob hBdd).trans hP

/-- The eventual upper-tail formulation required by the already checked
physical vanishing-deficit diagonal-cover theorem. -/
theorem pure_original_source_maximum_upper_tightness
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ d : ℕ in atTop,
      pureSourceMaximumFailure p hp L d ≤ ε := by
  obtain ⟨C,hC,hUpper⟩ := pure_original_source_maximum_upper p hp h
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  have hcp : 0 < cp :=
    SphericalPureCapCenteringIdentity.pureIntensityConstant_pos p (by omega)
  have hExp : Tendsto (fun L : ℝ => C*Real.exp (-cp*L)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,id_eq,mul_zero] using
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hcp))).const_mul C
  intro ε hε
  have hsmall := hExp.eventually (gt_mem_nhds hε)
  obtain ⟨L,hL,hsmallL⟩ := ((eventually_ge_atTop (0:ℝ)).and hsmall).exists
  refine ⟨L,hL,?_⟩
  have hBdd : IsBoundedUnder (· ≤ ·) atTop (pureSourceMaximumFailure p hp L) :=
    isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩
  exact (eventually_lt_of_limsup_lt ((hUpper L).trans_lt hsmallL) hBdd).mono
    fun _ hd => hd.le

end
end SlowEquilibration.SourcePureCaptureFixedCapEstimates
