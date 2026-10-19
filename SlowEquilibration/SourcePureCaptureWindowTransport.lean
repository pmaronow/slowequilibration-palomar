-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureFromCoarseCover
public import SlowEquilibration.SourcePureCriticalRadialWindowBridge
public import SlowEquilibration.SourceReductionConsumerAsymptotic

/-! The manuscript's exact `pc-window` transport. Original pure critical
points and center-field critical points agree pathwise; the prescribed
radial mark is automatic in each fixed centered energy window eventually.
The resulting band mass is the literal consumer band mass. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourcePureCaptureWindowTransport
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalGaussianJet SphericalMarkedWindows SphericalPureCenterFieldScale
open SphericalTAPCertificate PureStationarity PairConditionalDeterminantMoments
open SphericalPureCapSourceScalars SphericalPureCapCenteringIdentity
open SourcePureCaptureFixedCapEstimates SourcePureCaptureBandComplementBound
open SourcePureCaptureFromCoarseCover SourceReductionClosedBandGraph
open SourceReductionConsumerBandBound
open scoped Topology
set_option autoImplicit false

theorem pure_center_surfaceGradient_eq_original_scale
    (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {Q : ℝ} (hQ : 0 ≤ Q) (N : ℕ)
    (J : Disorder N (FiniteMixture.pure p hp α hα).maxDegree) (u : Vector N) :
    surfaceGradient (field (centerCoefficients
      (mixtureCoefficients (FiniteMixture.pure p hp α hα)) Q) J) u =
    (Real.sqrt Q)^p • surfaceGradient
      (field (mixtureCoefficients (FiniteMixture.pure p hp α hα)) J) u := by
  have heq := funext (pure_center_field_eq_original_scale p hp α hα hQ N J)
  rw [heq]
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient,real_inner_smul_left,inner_surfaceGradient,
    fderiv_const_mul ((field_contDiff _ J).differentiable (by simp) u)]
  rfl

/-- Inclusion in the original window holds in every dimension, before
the radial mark restriction is known to be automatic. -/
theorem pure_windowCenters_subset_original
    (p : ℕ) (hp : 4 ≤ p) {Q : ℝ} (hQ : 0 < Q)
    (d : ℕ) (m L : ℝ) (U : Set ℝ)
    (J : Disorder (d+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
    windowCenters (FiniteMixture.pure p (by omega) 1 (by positivity)) Q
      ((Real.sqrt Q)^p*m) ((Real.sqrt Q)^p*L) U J ⊆
    originalEnergyCriticalSet d (FiniteMixture.pure p (by omega) 1 (by positivity))
      (Icc (m-L) (m+L)) J := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr hQ) p
  intro u hu
  change (((‖u‖^2=(d+2:ℕ) ∧ _=0) ∧ _∈Icc (s*m-s*L) (s*m+s*L)) ∧ _) at hu
  have hg := pure_center_surfaceGradient_eq_original_scale p (by omega) 1
    (by positivity) hQ.le (d+2) J u
  have hcrit : surfaceGradient (field (mixtureCoefficients μ) J) u=0 := by
    rw [hg] at hu
    exact (smul_eq_zero.mp hu.1.1.2).resolve_left hs.ne'
  have hv := hu.1.2
  rw [pure_center_field_eq_original_scale p (by omega) 1 (by positivity) hQ.le] at hv
  refine ⟨hu.1.1.1,hcrit,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith [hv.1]
  · apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith [hv.2]

/-- At any fixed energy width the pure radial mark lies in every
neighborhood of the source contact mark, uniformly over the whole window. -/
theorem pure_original_window_radial_eventually
    (p : ℕ) (hp : 4 ≤ p) (Q L : ℝ) (U : Set ℝ)
    (hU : (p:ℝ)*(Real.sqrt Q)^p*pureEnergyConstant p (by omega) ∈ interior U) :
    ∀ᶠ d : ℕ in atTop, ∀ v : ℝ,
      v ∈ Icc (pureSourceCenter p hp d-L) (pureSourceCenter p hp d+L) →
      (p:ℝ)*((Real.sqrt Q)^p*v/(d+2:ℕ)) ∈ U := by
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let s := (Real.sqrt Q)^p
  have hUnhds : U ∈ 𝓝 ((p:ℝ)*s*ep) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hU) interior_subset
  have hf : ContinuousAt (fun e : ℝ => (p:ℝ)*s*e) ep := by fun_prop
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp (hf.tendsto hUnhds)
  have hcenter : ∀ᶠ d : ℕ in atTop,
      |pureSourceCenter p hp d-((d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp))| ≤ 0 :=
    .of_forall fun d => by simp only [pureSourceCenter,ep,cp,sub_self,abs_zero,le_refl]
  have hbox := source_logarithmic_center_offset_bounds
    (pureIntensityConstant_pos p (by omega)) (le_refl (0:ℝ)) (half_pos hρ)
    (pureSourceCenter p hp) hcenter (-L) L
  filter_upwards [hbox] with d hd
  intro v hv
  have hN : (0:ℝ)<(d+2:ℕ) := by positivity
  have hl : ep-ρ/2 ≤ v/(d+2:ℕ) := by
    apply (le_div_iff₀ hN).mpr
    simpa only [mul_comm,sub_eq_add_neg] using hd.1.trans hv.1
  have hr : v/(d+2:ℕ) ≤ ep+ρ/2 := by
    apply (div_le_iff₀ hN).mpr
    simpa only [mul_comm] using hv.2.trans hd.2
  have hmem : v/(d+2:ℕ) ∈ Metric.ball ep ρ := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hh := hball hmem
  change (p:ℝ)*s*(v/(d+2:ℕ)) ∈ U at hh
  convert hh using 1
  ring

/-- Literal `eq:pc-window`, simultaneously for every realized disorder.
No probabilistic genericity of the critical fiber is required. -/
theorem pure_windowCenters_eventually_eq_original
    (p : ℕ) (hp : 4 ≤ p) {Q : ℝ} (hQ : 0 < Q) (L : ℝ) (U : Set ℝ)
    (hU : (p:ℝ)*(Real.sqrt Q)^p*pureEnergyConstant p (by omega) ∈ interior U) :
    ∀ᶠ d : ℕ in atTop, ∀ J : Disorder (d+2)
      (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree,
      windowCenters (FiniteMixture.pure p (by omega) 1 (by positivity)) Q
        ((Real.sqrt Q)^p*pureSourceCenter p hp d) ((Real.sqrt Q)^p*L) U J =
      originalEnergyCriticalSet d (FiniteMixture.pure p (by omega) 1 (by positivity))
        (Icc (pureSourceCenter p hp d-L) (pureSourceCenter p hp d+L)) J := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr hQ) p
  filter_upwards [pure_original_window_radial_eventually p hp Q L U hU] with d hd
  intro J
  apply Set.Subset.antisymm (pure_windowCenters_subset_original p hp hQ d _ L U J)
  rintro u ⟨hu,hcrit,hv⟩
  change (((‖u‖^2=(d+2:ℕ) ∧ _=0) ∧
    _∈Icc (s*pureSourceCenter p hp d-s*L) (s*pureSourceCenter p hp d+s*L)) ∧ _)
  refine ⟨⟨⟨hu,?_⟩,?_⟩,?_⟩
  · rw [pure_center_surfaceGradient_eq_original_scale p (by omega) 1
      (by positivity) hQ.le,hcrit,smul_zero]
  · rw [pure_center_field_eq_original_scale p (by omega) 1 (by positivity) hQ.le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hv.1 hs.le,
      mul_le_mul_of_nonneg_left hv.2 hs.le]
  · change actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U
    rw [pure_actualScore_radial_eq_value (d+2) p (by omega) 1 (by positivity),actualValue,
      pure_center_field_eq_original_scale p (by omega) 1 (by positivity) hQ.le]
    exact hd _ hv

/-- Source consumer expectation, with the exact center-field normalization
and radial window U. -/
def pureConsumerUncovered (p : ℕ) (hp : 4 ≤ p)
    (β Q M b : ℝ) (U : Set ℝ) (d : ℕ) : ℝ :=
  ∫ J, SourceReductionConsumerAsymptotic.originalBandComplementMass
    (FiniteMixture.pure p (by omega) 1 (by positivity)) Q
    ((Real.sqrt Q)^p*pureSourceCenter p hp d) M b β U J
    ∂disorderLaw (d+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree

/-- Equality of actual Gibbs masses, including the consumer's explicit
sphere restriction. The microscopic width may vary with dimension. -/
theorem pureConsumerUncovered_eventually_eq_original
    (p : ℕ) (hp : 4 ≤ p) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (L : ℝ) (b : ℕ → ℝ) (U : Set ℝ)
    (hU : (p:ℝ)*(Real.sqrt Q)^p*pureEnergyConstant p (by omega) ∈ interior U) :
    (fun d => pureConsumerUncovered p hp β Q ((Real.sqrt Q)^p*L) (b d) U d) =ᶠ[atTop]
      (fun d => expectedOriginalBandComplementMass d
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β
        (pureSourceCenter p hp d) L (Real.sqrt Q) (b d)) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  filter_upwards [pure_windowCenters_eventually_eq_original p hp hQ L U hU] with d hd
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro J
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hsphere : ∀ᵐ x ∂gibbsLaw (d+2) β (field (mixtureCoefficients μ) J),
      ‖x‖^2=(d+2:ℕ) :=
    (sphereLaw_support (by omega : 1≤d+2)).filter_mono
      (gibbsLaw_absolutelyContinuous β (field (mixtureCoefficients μ) J)).ae_le
  filter_upwards [hsphere] with x hx
  apply propext
  apply not_congr
  change (∃ u, (J,u) ∈ windowCenterGraph μ Q
      ((Real.sqrt Q)^p*pureSourceCenter p hp d) ((Real.sqrt Q)^p*L) U ∧
      |overlap x u-Real.sqrt Q| ≤ b d) ∧ ‖x‖^2=(d+2:ℕ) ↔
    ∃ u ∈ originalEnergyCriticalSet d μ
      (Icc (pureSourceCenter p hp d-L) (pureSourceCenter p hp d+L)) J,
      overlap x u ∈ Icc (Real.sqrt Q-b d) (Real.sqrt Q+b d)
  have hcenter (u : Vector (d+2)) : (J,u) ∈ windowCenterGraph μ Q
      ((Real.sqrt Q)^p*pureSourceCenter p hp d) ((Real.sqrt Q)^p*L) U ↔
      u ∈ originalEnergyCriticalSet d μ
        (Icc (pureSourceCenter p hp d-L) (pureSourceCenter p hp d+L)) J :=
    Set.ext_iff.mp (hd J) u
  simp only [hcenter,hx,and_true,abs_le,Set.mem_Icc]
  constructor
  · rintro ⟨u,hu,hl,hr⟩
    exact ⟨u,hu,by linarith,by linarith⟩
  · rintro ⟨u,hu,hl,hr⟩
    exact ⟨u,hu,by linarith,by linarith⟩

end SlowEquilibration.SourcePureCaptureWindowTransport
end
