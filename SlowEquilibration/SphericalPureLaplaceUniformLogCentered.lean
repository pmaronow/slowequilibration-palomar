-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureLaplaceLocalData
public import SlowEquilibration.SphericalPureCapCenteringIdentity
public import SlowEquilibration.SphericalLatitudeNormalizationAsymptotic
public import SlowEquilibration.SourcePureLogPolynomialPhysical

/-! Uniform local Laplace asymptotics for the literal pure-model latitude
profile, including the exact logarithmic source centering and sphere coarea
normalization. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureLaplaceUniformLogCentered
noncomputable section
open Filter Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureLaplaceLocalData SphericalPureCapSourceScalars
open SphericalPureCapCenteringIdentity SourcePureLogPolynomialLaplace
open SourceUniformMonotoneParameter
open scoped Topology
set_option autoImplicit false

/-- Uniformity over `|t|≤L` of the exact log-centered local latitude mass
on any fixed microscopic set. The true spherical coarea prefactor is included. -/
theorem sourcePureLatitude_uniform_log_centered
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let q := Real.sqrt Q
    let φ := sourcePureLatitudeExponent p 1 Q β E
    let cp := pureIntensityConstant p (by omega)
    ∃ b κ : ℝ, 0 < b ∧ b < q ∧ 0 < κ ∧
      ∀ (S : Set ℝ) (L : ℝ),
        TendstoUniformlyOn
          (fun n t =>
            ((SphericalModel.latitudeNormalization (n+1)).toReal /
              Real.sqrt (n+2 : ℕ)) *
              centeredIntegral φ sourcePureLatitudeJacobian p β cp
                q (q-b) (q+b) S n t)
          (fun t => ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
            Real.exp (β*t*q^p) *
              (∫ u in S, Real.exp (-κ*u^2/2)))
          atTop (Icc (-L) L) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let q := Real.sqrt Q
  let φ := sourcePureLatitudeExponent p 1 Q β E
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  obtain ⟨b,c,M,κ,hb,hbq,hc,hM,hκ,hband,hφ,hA,hamp,henv,hstat,hcurv⟩ :=
    sourcePureLatitudeExponent_local_laplace_data p (by omega) 1 (by positivity) h
  have hqD : q ∈ Ioo (q-b) (q+b) := ⟨by linarith,by linarith⟩
  have hqmem : q ∈ Ioo (-1:ℝ) 1 := hband ⟨hqD.1.le,hqD.2.le⟩
  have hbandClosed : Icc (q-b) (q+b) ⊆ Icc (-1:ℝ) 1 := by
    intro z hz
    exact ⟨(hband hz).1.le,(hband hz).2.le⟩
  have hφmeas : Measurable φ := by
    dsimp only [φ]
    unfold sourcePureLatitudeExponent
      SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance
    fun_prop
  have hAmeas : Measurable sourcePureLatitudeJacobian := by
    unfold sourcePureLatitudeJacobian
    fun_prop
  have hstatWithin : derivWithin φ (Ioo (q-b) (q+b)) q = 0 := by
    rw [derivWithin_of_isOpen isOpen_Ioo hqD]
    exact hstat
  have hcurvWithin : iteratedDerivWithin 2 φ (Ioo (q-b) (q+b)) q = -κ := by
    rw [(iteratedDerivWithin_of_isOpen isOpen_Ioo) hqD]
    exact hcurv
  have hApos : ∀ z ∈ Icc (q-b) (q+b), 0 ≤ sourcePureLatitudeJacobian z := by
    intro z hz
    have hzi := hband hz
    have harg : 0 < 1-z^2 := by nlinarith [hzi.1,hzi.2]
    unfold sourcePureLatitudeJacobian
    exact (Real.rpow_pos_of_pos harg _).le
  have hzpos : ∀ z ∈ Icc (q-b) (q+b), 0 ≤ z := by
    intro z hz
    linarith [hbq,hz.1]
  have hcp : 0 < cp := pureIntensityConstant_pos p (by omega)
  have hnorm : Tendsto (fun n : ℕ =>
      (SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ)) atTop
      (𝓝 (1/Real.sqrt (2*Real.pi))) := by
    convert SphericalModel.latitudeNormalization_toReal_div_sqrt_tendsto.comp
      (tendsto_add_atTop_nat 1) using 1
    congr 1
  refine ⟨b,κ,hb,hbq,hκ,?_⟩
  intro S L
  have hmono (n : ℕ) : Monotone (fun t =>
      ((SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ)) *
        centeredIntegral φ sourcePureLatitudeJacobian p β cp
          q (q-b) (q+b) S n t) := by
    intro t₁ t₂ ht
    have hc₀ : 0 ≤ (SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ) :=
      div_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left
      ((centeredIntegral_monotone hφmeas hAmeas hc hM hamp
        ((abs_lt.mpr hqmem).le) hbandClosed henv hApos hzpos
        h.beta_pos.le hcp p n S) ht) hc₀
  have hpoint (t : ℝ) : Tendsto (fun n : ℕ =>
      ((SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ)) *
        centeredIntegral φ sourcePureLatitudeJacobian p β cp
          q (q-b) (q+b) S n t) atTop
      (𝓝 (((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
        Real.exp (β*t*q^p) *
          (∫ u in S, Real.exp (-κ*u^2/2)))) := by
    have hlocal := centeredIntegral_tendsto hφ hφmeas hA hAmeas
      hstatWithin hcurvWithin hqD.1 hqD.2 hqmem hc hM hamp
      hbandClosed henv p β cp t hcp S
    have hh := hnorm.mul hlocal
    convert hh using 1
    rw [sourcePureLatitudeJacobian_contact h.overlap_range.1.le]
    ring
  have hf : Continuous (fun t : ℝ =>
      ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
        Real.exp (β*t*q^p) *
          (∫ u in S, Real.exp (-κ*u^2/2))) := by fun_prop
  have huni := uniform_on_compact_of_monotone (S:=Icc (-L) L)
    (fun n t =>
      ((SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ)) *
        centeredIntegral φ sourcePureLatitudeJacobian p β cp
          q (q-b) (q+b) S n t)
    (fun t => ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
      Real.exp (β*t*q^p) *
        (∫ u in S, Real.exp (-κ*u^2/2))) hmono hf hpoint isCompact_Icc
  simpa only [μ,E,q,φ,cp] using huni

end
end SlowEquilibration.SphericalPureLaplaceUniformLogCentered
