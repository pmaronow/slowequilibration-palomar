-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetCertificateSecondMoment
public import SlowEquilibration.SphericalTAPMixedPalmDeterminantQuadraticReduction

@[expose] public section

/-! Cauchy assembly for the actual original-tensor quadratic latitude bank
and the actual conditioned Hessian determinant. The certificate supplies the
uniform overlap constant; the physical GOE law supplies the determinant
constant. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter SphericalModel ConditionedDeterminantMoments
open SphericalTAPCertificate SphericalTAPMixedPalmDeterminantQuadraticReduction
open SphericalTAPCriticalAnalyticNeighborhood
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- The original quadratic bank is Borel measurable as a function of the
tensor disorder. -/
theorem quadraticBankPartition_measurable
    {d : ℕ} (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2)) :
    Measurable (quadraticBankPartition μ a β u) := by
  exact (quadraticBankPoint_joint_measurable μ a β u).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- The exact mixed-Palm quadratic-bank second moment and the determinant
moment give a uniform bound on their correlated product throughout the
certificate's latitude band and a fixed spectral gap. -/
theorem quadraticBankPartition_certificate_determinant_cauchy
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {β x Q : ℝ} (h : Certificate μ β x Q)
    {g : ℝ} (hg : 0 < g) :
    let K := (2 : ℝ)^2 * Real.exp
      (4*(Q^2*μ.xi2 Q)*(2 : ℝ)^2/g^2)
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
          (mark : EuclideanSpace ℝ (Fin 2)),
          2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ mark 1 →
          ∀ (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Set.Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            let Z₂ := quadraticBankPartition μ a β u
            let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
            let detMean := ∫ J, intrinsicDet μ Q u J ∂mixedLaw μ Q u hu mark
            Integrable (fun J => intrinsicDet μ Q u J * Z₂ J)
              (mixedLaw μ Q u hu mark) ∧
            (∫ J, intrinsicDet μ Q u J * Z₂ J
              ∂mixedLaw μ Q u hu mark) ≤
                detMean*m*Real.sqrt K*Real.sqrt C := by
  have hμ : 3 ≤ μ.minDegree := by have := h.min_degree; omega
  obtain ⟨b₀,C,hb₀,hb₀Q,hC,hbank⟩ :=
    quadraticBankPartition_certificate_uniform_secondMoment μ hμ h
  have hdet := mixed_determinant_quadratic_bank_cauchy_eventually
    μ h.overlap_range.1 hnp hg
  refine ⟨b₀,C,hb₀,hb₀Q,hC,?_⟩
  filter_upwards [hbank,hdet] with d hbd hdd
  intro u hu mark hmark b hb hbb a ha
  let ν := mixedLaw μ Q u hu mark
  let Z₂ := quadraticBankPartition μ a β u
  let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
  have hm : 0 < m := Real.exp_pos _
  have hZpos : ∀ J, 0 ≤ Z₂ J := by
    intro J
    exact integral_nonneg (fun y => (Real.exp_pos _).le)
  have hZmeas : Measurable Z₂ := quadraticBankPartition_measurable μ a β u
  have hZsq : Integrable (fun J => (Z₂ J)^2) ν :=
    quadraticBankPartition_physicalMixedPalm_sq_integrable μ hμ Q a β u hu mark
  have hnormalized (J : Disorder (d+2) μ.maxDegree) :
      (Z₂ J/m)^2 = (m⁻¹)^2*(Z₂ J)^2 := by
    rw [div_eq_mul_inv]
    ring
  have hZint : Integrable (fun J => (Z₂ J/m)^2) ν := by
    convert hZsq.const_mul ((m⁻¹)^2) using 1
    funext J
    exact hnormalized J
  have hbankBound : (∫ J, (Z₂ J)^2 ∂ν) ≤ C*m^2 := by
    have hh := hbd u hu mark b hb hbb a ha
    rw [quadraticBankPartition_physicalMixedPalm_mean μ hμ Q a β u hu mark] at hh
    simpa only [Z₂,ν,m] using hh
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
  exact hdd u hu mark hmark Z₂ hm hZpos hZmeas hZint hZbound

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
