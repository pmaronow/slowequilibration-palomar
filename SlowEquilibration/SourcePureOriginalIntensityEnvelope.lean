-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureOriginalEdgeMargin
public import SlowEquilibration.SourcePureAllCriticalIntensityEnvelope
public import SlowEquilibration.SphericalPureCapCenteringIdentity

/-! An intensity envelope for the actual amplitude-one pure field at its
ground-state logarithmic centering. -/

@[expose] public section
namespace SlowEquilibration.SourcePureOriginalIntensityEnvelope
noncomputable section
open Set Filter SphericalMarkedWindows SphericalTAPCertificate
open TwoAtomStationarity PureStationarity
open SphericalPureCapSourceScalars
open SphericalPureCapCenteringIdentity
open SourcePureOriginalComplexityEnvelope
open ExpectedTailCentering
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_criticalPhysicalIntensity_centered_envelope
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {δ g Z M : ℝ} (_hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt ((FiniteMixture.pure p (by omega) 1 (by positivity)).xi2 1)+g ≤
      (p : ℝ)*(pureEnergyConstant p (by omega)-δ))
    (hRight : (p : ℝ)*(pureEnergyConstant p (by omega)+δ) ≤ Z)
    (m : ℕ → ℝ) (_hM : 0 ≤ M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*pureEnergyConstant p (by omega)-
        Real.log (n+2 : ℕ)/(2*pureIntensityConstant p (by omega)))| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ H ∈ Icc ((n+2 : ℕ)*(pureEnergyConstant p (by omega)-δ))
        ((n+2 : ℕ)*(pureEnergyConstant p (by omega)+δ)),
        (pureCriticalPhysicalIntensity n p (by omega) 1 (by positivity) 1 H).toReal ≤
          C*Real.exp ((pureIntensityConstant p (by omega))*(m n-H)) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := pureEnergyConstant p (by omega : 3 ≤ p)
  let c₀ := pureIntensityConstant p (by omega : 3 ≤ p)
  have hc₀ : 0 < c₀ := pureIntensityConstant_pos p (by omega)
  obtain ⟨_,C₀,_,hC₀,hPref⟩ :=
    actual_pure_intensity_prefactors p (by omega) 1 (by positivity)
      (show (0:ℝ)<1 by norm_num) (Z := Z) hg
  let C := C₀*Real.exp (c₀*M)
  have hC : 0 < C := mul_pos hC₀ (Real.exp_pos _)
  refine ⟨C,hC,?_⟩
  filter_upwards [hcenter] with n hn
  intro H hH
  let N : ℝ := (n+2 : ℕ)
  let e : ℝ := H/N
  let t : ℝ := m n-(N*E-Real.log N/(2*c₀))
  have hN : 0 < N := by dsimp [N]; positivity
  have he : N*e=H := by dsimp [e]; field_simp
  have heBand : e ∈ Icc (E-δ) (E+δ) := by
    dsimp [e,N,E] at *
    constructor
    · exact (le_div_iff₀ (by positivity : (0:ℝ)<(n+2:ℕ))).mpr (by
        nlinarith [hH.1])
    · exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+2:ℕ))).mpr (by
        nlinarith [hH.2])
  have hmark : (p:ℝ)*e ∈ Icc
      (2*Real.sqrt (μ.xi2 1)+g) Z := by
    have hpnonneg : 0 ≤ (p:ℝ) := by positivity
    constructor
    · exact hLeft.trans (mul_le_mul_of_nonneg_left heBand.1 hpnonneg)
    · exact (mul_le_mul_of_nonneg_left heBand.2 hpnonneg).trans hRight
  have hmark' : (p:ℝ)*e ∈ Icc
      (2*Real.sqrt (1^2*μ.xi2 1)+g) Z := by
    simpa only [one_pow, one_mul] using hmark
  have hUpper := (hPref n e hmark').2
  have hPhys : pureCriticalPhysicalIntensity n p (by omega) 1 (by positivity) 1 H ≤
      ENNReal.ofReal (C₀*(Real.sqrt N)⁻¹ *
        Real.exp (N*pureMarkedComplexity p (by omega) 1 (by positivity) 1 e)) := by
    have hMul := mul_le_mul_right hUpper (ENNReal.ofReal N⁻¹)
    simp only [pureCriticalPhysicalIntensity, N] at hMul ⊢
    rw [inverse_sqrt_dimension_prefactor] at hMul
    exact hMul
  have hPhysReal :
      (pureCriticalPhysicalIntensity n p (by omega) 1 (by positivity) 1 H).toReal ≤
      C₀/(Real.sqrt N)*Real.exp
        (N*pureMarkedComplexity p (by omega) 1 (by positivity) 1 e) := by
    have hh := ENNReal.toReal_mono (by simp) hPhys
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    simpa only [div_eq_mul_inv] using hh
  have hLoss := pure_original_complexity_global_linear_loss p hp h e
  have hExp : Real.exp
      (N*pureMarkedComplexity p (by omega) 1 (by positivity) 1 e) ≤
      Real.exp (c₀*(N*E-H)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hLoss hN.le
    dsimp [E,c₀] at *
    nlinarith [hh,he]
  have ht : |t| ≤ M := by
    simpa only [t,N,E,c₀] using hn
  have hscale : Real.exp (c₀*(N*E-m n))/Real.sqrt N =
      Real.exp (-c₀*t) := by
    have hh := reference_scale hN hc₀ t
    convert hh using 1
    congr 1
    dsimp [t]
    ring
  have htExp : Real.exp (-c₀*t) ≤ Real.exp (c₀*M) :=
    Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp ht).1])
  calc
    (pureCriticalPhysicalIntensity n p (by omega) 1 (by positivity) 1 H).toReal ≤
        C₀/Real.sqrt N * Real.exp
          (N*pureMarkedComplexity p (by omega) 1 (by positivity) 1 e) := hPhysReal
    _ ≤ C₀/Real.sqrt N*Real.exp (c₀*(N*E-H)) := by
      exact mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = C₀*(Real.exp (c₀*(N*E-m n))/Real.sqrt N)*
          Real.exp (c₀*(m n-H)) := by
      have hid : Real.exp (c₀*(N*E-H)) =
          Real.exp (c₀*(N*E-m n))*Real.exp (c₀*(m n-H)) := by
        rw [←Real.exp_add]
        congr 1
        ring
      rw [hid]
      ring
    _ = C₀*Real.exp (-c₀*t)*Real.exp (c₀*(m n-H)) := by rw [hscale]
    _ ≤ C*Real.exp (c₀*(m n-H)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htExp hC₀.le) (Real.exp_pos _).le

end
end SlowEquilibration.SourcePureOriginalIntensityEnvelope
