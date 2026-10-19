-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPurePalmDeterminantQuadraticReduction
public import SlowEquilibration.SphericalQuadraticLatitudeJetBankDeterminantCauchy

@[expose] public section

/-! Sharp Cauchy bound for the genuine original-tensor quadratic bank and
conditioned intrinsic Hessian determinant under the proper-pure Palm law. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter SphericalModel SphericalGaussianJet
open ConditionedDeterminantMoments SphericalMarkedWindows
open SphericalTAPCertificate
open SphericalTAPCriticalAnalyticNeighborhood
open SphericalTAPPurePalmDeterminantQuadraticReduction
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- Certificate-uniform determinant-times-quadratic-bank estimate at the
literal pure value/gradient conditioning. The bank remains correlated with
the Hessian; its actual second moment and Cauchy's inequality control it. -/
theorem quadraticBankPartition_pure_certificate_determinant_cauchy
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let K := (2 : ℝ)^2 * Real.exp
      (4*(Q^2*μ.xi2 Q)*(2 : ℝ)^2/g^2)
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (e : ℝ),
          2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*e →
          ∀ (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Set.Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            let Z₂ := quadraticBankPartition μ a β u
            let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
            let detMean := ∫ J, intrinsicDet μ Q u J
              ∂pureLaw p hp alpha halpha Q u hu e
            Integrable (fun J => intrinsicDet μ Q u J * Z₂ J)
              (pureLaw p hp alpha halpha Q u hu e) ∧
            (∫ J, intrinsicDet μ Q u J * Z₂ J
              ∂pureLaw p hp alpha halpha Q u hu e) ≤
                detMean*m*Real.sqrt K*Real.sqrt C := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have hμ : 3 ≤ μ.minDegree := by
    have hh : 4 ≤ μ.minDegree := h.min_degree
    omega
  obtain ⟨b₀,C,hb₀,hb₀Q,hC,hbank⟩ :=
    quadraticBankPartition_pure_certificate_uniform_secondMoment μ hμ h
  have hdet := pure_determinant_quadratic_bank_cauchy_eventually
    p hp alpha halpha h.overlap_range.1 hg
  refine ⟨b₀,C,hb₀,hb₀Q,hC,?_⟩
  filter_upwards [hbank,hdet] with d hbd hdd
  intro u hu e he b hb hbb a ha
  let ν := pureLaw p hp alpha halpha Q u hu e
  let Z₂ := quadraticBankPartition μ a β u
  let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
  have hm : 0 < m := Real.exp_pos _
  have hZpos : ∀ J, 0 ≤ Z₂ J := by
    intro J
    exact integral_nonneg (fun y => (Real.exp_pos _).le)
  have hZmeas : Measurable Z₂ := quadraticBankPartition_measurable μ a β u
  have hν : ν = valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu e :=
    pureLaw_eq_valueConditionedLaw p hp alpha halpha Q u hu e
  have hZsq : Integrable (fun J => (Z₂ J)^2) ν := by
    rw [hν]
    exact quadraticBankPartition_physicalPurePalm_sq_integrable μ hμ Q a β u hu e
  have hnormalized (J : Disorder (d+2) μ.maxDegree) :
      (Z₂ J/m)^2 = (m⁻¹)^2*(Z₂ J)^2 := by
    rw [div_eq_mul_inv]
    ring
  have hZint : Integrable (fun J => (Z₂ J/m)^2) ν := by
    convert hZsq.const_mul ((m⁻¹)^2) using 1
    funext J
    exact hnormalized J
  have hbankBound : (∫ J, (Z₂ J)^2 ∂ν) ≤ C*m^2 := by
    have hh := hbd u hu e b hb hbb a ha
    rw [quadraticBankPartition_physicalPurePalm_mean μ hμ Q a β u hu e] at hh
    simpa only [Z₂,ν,hν,m] using hh
  have hZbound : (∫ J, (Z₂ J/m)^2 ∂ν) ≤ C := by
    have hi : (∫ J, (Z₂ J/m)^2 ∂ν) =
        (m⁻¹)^2 * (∫ J, (Z₂ J)^2 ∂ν) := by
      simp_rw [hnormalized]
      rw [integral_const_mul]
    rw [hi]
    calc
      _ ≤ (m⁻¹)^2*(C*m^2) :=
        mul_le_mul_of_nonneg_left hbankBound (sq_nonneg _)
      _ = C := by field_simp
  exact hdd u hu e he Z₂ hm hZpos hZmeas hZint hZbound

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
