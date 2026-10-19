module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalZeroMode

@[expose] public section

/-! # The actual simple constant mode and strictly positive higher modes -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open SphericalModel SphericalAging.HardSphereDynamics
open scoped InnerProductSpace Topology ContDiff

lemma gibbsConstant_smul_one {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (c : ℝ) :
    gibbsConstant hN β H hH c = c • gibbsConstant hN β H hH 1 := by
  unfold gibbsConstant
  rw [← gibbsToL2_smul hN β H hH (fun _ => 1) continuous_const c]
  apply gibbsToL2_congr
  apply ae_of_all
  intro x
  simp

lemma gibbsConstant_eq_zero_iff {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (c : ℝ) :
    gibbsConstant hN β H hH c = 0 ↔ c = 0 := by
  constructor
  · intro hz
    have hn := gibbsConstant_norm_sq hN β H hH c
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    exact sq_eq_zero_iff.mp hn.symm
  · rintro rfl
    rw [gibbsConstant_smul_one, zero_smul]

namespace SphericalSpectralData
variable {N : ℕ} {hN : 2 ≤ N} {β : ℝ} {H : Vector N → ℝ} {hH : Continuous H}

/-- The actual zeroth basis vector spans exactly the genuine constants. -/
theorem basis_zero_constant (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) :
    ∃ c : ℝ, c ≠ 0 ∧ D.basis 0 = c • gibbsConstant (show 1 ≤ N by omega) β H hH 1 := by
  have he : sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis 0) = D.basis 0 := by
    rw [D.eigen, D.resolventEigenvalue_zero hHC, one_smul]
  obtain ⟨c, hc⟩ := (sphericalL2Resolvent_fixed_iff_constant hN β hHC (D.basis 0)).mp he
  have hne : c ≠ 0 := by
    intro hz
    have hzero := (gibbsConstant_eq_zero_iff (show 1 ≤ N by omega) β H hH c).mpr hz
    exact (D.basis.orthonormal.ne_zero 0) (hc.trans hzero)
  exact ⟨c, hne, hc.trans (gibbsConstant_smul_one (show 1 ≤ N by omega) β H hH c)⟩

/-- The genuine actual ordered spherical spectrum has exactly one zero
mode. This uses the proved completed-energy rigidity, not eigenregularity. -/
theorem eigenvalue_eq_zero_iff (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (n : ℕ) : D.eigenvalue n = 0 ↔ n = 0 := by
  constructor
  · intro hn
    by_contra hn0
    have hm : D.resolventEigenvalue n = 1 := by
      have hi : (D.resolventEigenvalue n)⁻¹ = 1 := sub_eq_zero.mp hn
      have hh := inv_mul_cancel₀ (D.bounds n).1.ne'
      rw [hi, one_mul] at hh
      exact hh
    have he : sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis n) = D.basis n := by
      rw [D.eigen, hm, one_smul]
    obtain ⟨c, hc⟩ := (sphericalL2Resolvent_fixed_iff_constant hN β hHC (D.basis n)).mp he
    rw [gibbsConstant_smul_one] at hc
    obtain ⟨c₀, hc₀, hzero⟩ := D.basis_zero_constant hHC
    have horth : inner ℝ (D.basis n) (D.basis 0) = 0 := by
      simpa only [if_neg hn0] using (orthonormal_iff_ite.mp D.basis.orthonormal n 0)
    rw [hc, hzero, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, gibbsConstant_one_norm, one_pow, mul_one] at horth
    have hcz : c = 0 := (mul_eq_zero.mp horth).resolve_right hc₀
    rw [hcz, zero_smul] at hc
    exact (D.basis.orthonormal.ne_zero n) hc
  · rintro rfl
    exact D.eigenvalue_zero hHC

/-- All modes after the true constant mode have strictly positive actual
generator eigenvalues. -/
theorem eigenvalue_pos_of_ne_zero (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) {n : ℕ} (hn : n ≠ 0) : 0 < D.eigenvalue n := by
  have hz : D.eigenvalue n ≠ 0 := fun h => hn ((D.eigenvalue_eq_zero_iff hHC n).mp h)
  exact lt_of_le_of_ne (D.eigenvalue_nonneg n) hz.symm

theorem eigenvalue_one_pos (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) : 0 < D.eigenvalue 1 := D.eigenvalue_pos_of_ne_zero hHC (by decide)

/-- Spectral centering is exactly orthogonality to actual constants,
proved using the true one-dimensional zero mode. -/
theorem centered_iff_constant_orthogonal (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    D.toSemigroupData.Centered f ↔
      inner ℝ (gibbsConstant (show 1 ≤ N by omega) β H hH 1) f = 0 := by
  obtain ⟨c, hc, hb⟩ := D.basis_zero_constant hHC
  constructor
  · intro hf
    have hz := hf 0 (D.eigenvalue_zero hHC)
    change inner ℝ (D.basis 0) f = 0 at hz
    rw [hb, real_inner_smul_left] at hz
    exact (mul_eq_zero.mp hz).resolve_left hc
  · intro hf
    intro n hn
    have hn0 := (D.eigenvalue_eq_zero_iff hHC n).mp hn
    subst n
    change inner ℝ (D.basis 0) f = 0
    rw [hb, real_inner_smul_left, hf, mul_zero]

/-- Spectral centering is exactly zero actual Gibbs mean. -/
theorem centered_iff_integral_zero (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    D.toSemigroupData.Centered f ↔ (∫ x, f x ∂gibbsLaw N β H) = 0 := by
  rw [D.centered_iff_constant_orthogonal hHC f, real_inner_comm]
  rw [gibbsConstant, gibbsToL2_inner_right]
  simp only [mul_one]

end SphericalSpectralData
end
end SlowEquilibration.SphericalForm
