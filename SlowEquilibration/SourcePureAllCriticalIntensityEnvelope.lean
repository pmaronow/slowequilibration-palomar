-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureOnePointContactEnvelope
public import SlowEquilibration.SphericalPureLocalMaxPhysicalIntensity
public import SlowEquilibration.ExpectedLogarithmicCentering

@[expose] public section

/-! The true proper-pure all-critical Kac--Rice density has an integrable
lower-energy envelope around every source logarithmic centering. The proof
uses the scalar pure mark law and the ordinary absolute GOE determinant. -/

namespace SlowEquilibration.SphericalMarkedWindows
noncomputable section
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Proper-pure source Lemma 12.16 for any logarithmically centered physical
energy sequence in a fixed exterior value box. The rate is the sharper
`β*x < β`; there is no singular two-mark Gaussian density. -/
theorem sourcePure_allCriticalPhysicalIntensity_centered_envelope
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    {δ g Z M : ℝ} (_hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp alpha halpha) β x Q-δ))
    (hRight : (p : ℝ)*(markE (FiniteMixture.pure p hp alpha halpha) β x Q+δ) ≤ Z)
    (m : ℕ → ℝ) (_hM : 0 ≤ M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp alpha halpha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ β*x < β ∧ ∀ᶠ n : ℕ in atTop,
      ∀ H ∈ Icc ((n+2 : ℕ)*(markE
          (FiniteMixture.pure p hp alpha halpha) β x Q-δ))
        ((n+2 : ℕ)*(markE
          (FiniteMixture.pure p hp alpha halpha) β x Q+δ)),
        (pureCriticalPhysicalIntensity n p hp alpha halpha Q H).toReal ≤
          C*Real.exp ((β*x)*(m n-H)) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let c₀ := β*x
  have hc₀ : 0 < c₀ := mul_pos h.beta_pos h.weight_range.1
  have hc₀β : c₀ < β := mul_lt_of_lt_one_right h.beta_pos h.weight_range.2
  obtain ⟨_,C₀,_,hC₀,hPref⟩ :=
    actual_pure_intensity_prefactors p hp alpha halpha h.overlap_range.1
      (Z := Z) hg
  let C := C₀*Real.exp (c₀*M)
  have hC : 0 < C := mul_pos hC₀ (Real.exp_pos _)
  refine ⟨C,hC,hc₀β,?_⟩
  filter_upwards [hcenter] with n hn
  intro H hH
  let N : ℝ := (n+2 : ℕ)
  let e : ℝ := H/N
  let t : ℝ := m n-(N*E-Real.log N/(2*c₀))
  have hN : 0 < N := by dsimp [N]; positivity
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have he : N*e=H := by dsimp [e]; field_simp
  have heBand : e ∈ Icc (E-δ) (E+δ) := by
    dsimp [e,N,E] at *
    constructor
    · exact (le_div_iff₀ (by positivity : (0:ℝ)<(n+2:ℕ))).mpr (by
        nlinarith [hH.1])
    · exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+2:ℕ))).mpr (by
        nlinarith [hH.2])
  have hmark : (p:ℝ)*e ∈ Icc
      (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z := by
    have hpnonneg : 0 ≤ (p:ℝ) := by positivity
    constructor
    · exact hLeft.trans (mul_le_mul_of_nonneg_left heBand.1 hpnonneg)
    · exact (mul_le_mul_of_nonneg_left heBand.2 hpnonneg).trans hRight
  have hUpper := (hPref n e hmark).2
  have hPhys : pureCriticalPhysicalIntensity n p hp alpha halpha Q H ≤
      ENNReal.ofReal (C₀*(Real.sqrt N)⁻¹ *
        Real.exp (N*pureMarkedComplexity p hp alpha halpha Q e)) := by
    have hMul := mul_le_mul_right hUpper (ENNReal.ofReal N⁻¹)
    simp only [pureCriticalPhysicalIntensity, N] at hMul ⊢
    rw [inverse_sqrt_dimension_prefactor] at hMul
    exact hMul
  have hPhysReal : (pureCriticalPhysicalIntensity n p hp alpha halpha Q H).toReal ≤
      C₀/(Real.sqrt N)*Real.exp (N*pureMarkedComplexity p hp alpha halpha Q e) := by
    have hh := ENNReal.toReal_mono (by simp) hPhys
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    simpa only [div_eq_mul_inv] using hh
  have hLoss := sourcePureMarkedComplexity_global_linear_loss p hp alpha halpha h e
  have hExp : Real.exp (N*pureMarkedComplexity p hp alpha halpha Q e) ≤
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
    (pureCriticalPhysicalIntensity n p hp alpha halpha Q H).toReal ≤
        C₀/Real.sqrt N * Real.exp (N*pureMarkedComplexity p hp alpha halpha Q e) := hPhysReal
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
end SlowEquilibration.SphericalMarkedWindows
