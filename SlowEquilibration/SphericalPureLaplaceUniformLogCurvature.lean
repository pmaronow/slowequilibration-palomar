-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureLaplaceUniformLogCenteredSubband
public import SlowEquilibration.SphericalPureCapRawProfileIdentity
public import SlowEquilibration.SphericalPureCapCenteringIdentity
public import SlowEquilibration.SphericalLatitudeNormalizationAsymptotic
public import SlowEquilibration.SourcePureLogPolynomialPhysical

/-! Uniform local Laplace asymptotics for the literal pure-model latitude
profile, including the exact logarithmic source centering and sphere coarea
normalization. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureLaplaceUniformLogCurvature
noncomputable section
open Filter Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureLaplaceLocalData SphericalPureCapSourceScalars
open SphericalPureCapCenteringIdentity SourcePureLogPolynomialLaplace
open SourceUniformMonotoneParameter
open scoped Topology
set_option autoImplicit false

/-- The literal printed §9 pure latitude exponent `Λ`. -/
def purePrintedLatitudeProfile (p : ℕ) (hp : 4 ≤ p) (β z : ℝ) : ℝ :=
  β*PureStationarity.pureEnergyConstant p (by omega)*z^p +
    Real.log (1-z^2)/2+
      PureStationarity.pureResidualCoefficient p β z/2

/-- The source curvature `k_* = -Λ''(√Q)`. -/
def purePrintedKStar (p : ℕ) (hp : 4 ≤ p) (β Q : ℝ) : ℝ :=
  -iteratedDeriv 2 (purePrintedLatitudeProfile p hp β) (Real.sqrt Q)

/-- Uniformity over `|t|≤L` of the exact log-centered local latitude mass
on any fixed microscopic set. The true spherical coarea prefactor is included. -/
theorem sourcePureLatitude_uniform_log_centered_exact_curvature
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let q := Real.sqrt Q
    let φ := sourcePureLatitudeExponent p 1 Q β E
    let cp := pureIntensityConstant p (by omega)
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ b₀ < q ∧ q+b₀ < 1 ∧ 0 < κ ∧
      κ = purePrintedKStar p hp β Q ∧
      ∀ b : ℝ, 0 < b → b ≤ b₀ →
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
  obtain ⟨b₀,c,M,κ,hb,hbq,hc,hM,hκ,hband,hφ,hA,hamp,henv,hstat,hcurv⟩ :=
    sourcePureLatitudeExponent_local_laplace_data p (by omega) 1 (by positivity) h
  have hb₀r : q+b₀ < 1 :=
    (hband ⟨by linarith [hb],le_refl _⟩).2
  have hprofile : purePrintedLatitudeProfile p hp β = φ := by
    funext z
    exact (SphericalPureCapRawProfileIdentity.sourcePure_cap_printed_profile p hp h z).symm
  have hκEq : κ = purePrintedKStar p hp β Q := by
    unfold purePrintedKStar
    rw [hprofile,hcurv]
    ring
  refine ⟨b₀,κ,hb,hbq,hb₀r,hκ,hκEq,?_⟩
  intro b hbN hbb₀
  have hbqN : b < q := lt_of_le_of_lt hbb₀ hbq
  have hsub : Icc (q-b) (q+b) ⊆ Icc (q-b₀) (q+b₀) := by
    intro z hz
    exact ⟨by linarith [hbb₀,hz.1],by linarith [hbb₀,hz.2]⟩
  have hopen : Ioo (q-b) (q+b) ⊆ Ioo (q-b₀) (q+b₀) := by
    intro z hz
    exact ⟨by linarith [hbb₀,hz.1],by linarith [hbb₀,hz.2]⟩
  have hbandN : Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 :=
    fun z hz => hband (hsub hz)
  have hφN : ContDiffOn ℝ 2 φ (Ioo (q-b) (q+b)) := hφ.mono hopen
  have hAN : ContinuousOn sourcePureLatitudeJacobian (Icc (q-b) (q+b)) :=
    hA.mono hsub
  have hampN : ∀ z ∈ Icc (q-b) (q+b),
      |sourcePureLatitudeJacobian z| ≤ M := fun z hz => hamp z (hsub hz)
  have henvN : ∀ z ∈ Icc (q-b) (q+b), φ z ≤ φ q-c*(z-q)^2 :=
    fun z hz => henv z (hsub hz)
  have hqD : q ∈ Ioo (q-b) (q+b) := ⟨by linarith,by linarith⟩
  have hqmem : q ∈ Ioo (-1:ℝ) 1 := hbandN ⟨hqD.1.le,hqD.2.le⟩
  have hbandClosed : Icc (q-b) (q+b) ⊆ Icc (-1:ℝ) 1 := by
    intro z hz
    exact ⟨(hbandN hz).1.le,(hbandN hz).2.le⟩
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
    have hzi := hbandN hz
    have harg : 0 < 1-z^2 := by nlinarith [hzi.1,hzi.2]
    unfold sourcePureLatitudeJacobian
    exact (Real.rpow_pos_of_pos harg _).le
  have hzpos : ∀ z ∈ Icc (q-b) (q+b), 0 ≤ z := by
    intro z hz
    linarith [hbqN,hz.1]
  have hcp : 0 < cp := pureIntensityConstant_pos p (by omega)
  have hnorm : Tendsto (fun n : ℕ =>
      (SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ)) atTop
      (𝓝 (1/Real.sqrt (2*Real.pi))) := by
    convert SphericalModel.latitudeNormalization_toReal_div_sqrt_tendsto.comp
      (tendsto_add_atTop_nat 1) using 1
    congr 1
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
      ((centeredIntegral_monotone hφmeas hAmeas hc hM hampN
        ((abs_lt.mpr hqmem).le) hbandClosed henvN hApos hzpos
        h.beta_pos.le hcp p n S) ht) hc₀
  have hpoint (t : ℝ) : Tendsto (fun n : ℕ =>
      ((SphericalModel.latitudeNormalization (n+1)).toReal /
        Real.sqrt (n+2 : ℕ)) *
        centeredIntegral φ sourcePureLatitudeJacobian p β cp
          q (q-b) (q+b) S n t) atTop
      (𝓝 (((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
        Real.exp (β*t*q^p) *
          (∫ u in S, Real.exp (-κ*u^2/2)))) := by
    have hlocal := centeredIntegral_tendsto hφN hφmeas hAN hAmeas
      hstatWithin hcurvWithin hqD.1 hqD.2 hqmem hc hM hampN
      hbandClosed henvN p β cp t hcp S
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

/-- The printed Gaussian curvature is strictly positive at the literal
proper-pure contact. -/
theorem purePrintedKStar_pos
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    0 < purePrintedKStar p hp β Q := by
  obtain ⟨b₀,κ,hb₀,hb₀q,hb₀r,hκ,hκEq,_⟩ :=
    sourcePureLatitude_uniform_log_centered_exact_curvature p hp h
  rw [← hκEq]
  exact hκ

end
end SlowEquilibration.SphericalPureLaplaceUniformLogCurvature
