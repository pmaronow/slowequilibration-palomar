module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalSimpleSpectrum

@[expose] public section

/-! # Genuine ordered spherical eigenbasis with the literal constant vector -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open Set MeasureTheory Filter
open SphericalModel
open scoped InnerProductSpace Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A global sign isometry gives a genuine Hilbert basis. -/
def negHilbertBasis (b : HilbertBasis ℕ ℝ E) : HilbertBasis ℕ ℝ E :=
  HilbertBasis.ofRepr ((LinearIsometryEquiv.neg ℝ).trans b.repr)

@[simp] theorem negHilbertBasis_apply (b : HilbertBasis ℕ ℝ E) (n : ℕ) :
    negHilbertBasis b n = -b n := by
  rw [← (negHilbertBasis b).repr_symm_single, ← b.repr_symm_single]
  simp only [negHilbertBasis, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_neg,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_neg]

namespace SphericalSpectralData
variable {N : ℕ} {hN : 2 ≤ N} {β : ℝ} {H : Vector N → ℝ} {hH : Continuous H}

/-- A genuine sign change preserves every literal resolvent eigen equation. -/
def negBasis (D : SphericalSpectralData hN β H hH) : SphericalSpectralData hN β H hH where
  basis := negHilbertBasis D.basis
  resolventEigenvalue := D.resolventEigenvalue
  bounds := D.bounds
  antitone := D.antitone
  tendsto_zero := D.tendsto_zero
  eigen n := by simp only [negHilbertBasis_apply, map_neg, D.eigen, smul_neg]
  generator_monotone := D.generator_monotone
  generator_tendsto_atTop := D.generator_tendsto_atTop

theorem basis_zero_eq_one_or_neg (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) :
    D.basis 0 = gibbsConstant (show 1 ≤ N by omega) β H hH 1 ∨
      D.basis 0 = -gibbsConstant (show 1 ≤ N by omega) β H hH 1 := by
  obtain ⟨c, hc, hb⟩ := D.basis_zero_constant hHC
  have hn : inner ℝ (D.basis 0) (D.basis 0) = 1 := by
    simpa using (orthonormal_iff_ite.mp D.basis.orthonormal 0 0)
  rw [hb, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    gibbsConstant_one_norm, one_pow, mul_one] at hn
  rcases (mul_self_eq_one_iff).mp hn with h | h
  · left
    simpa only [h, one_smul] using hb
  · right
    simpa only [h, neg_smul, one_smul] using hb

/-- Normalize the already proved actual ordered eigenbasis so its zeroth
vector is the literal constant one. -/
def normalized (D : SphericalSpectralData hN β H hH) : SphericalSpectralData hN β H hH := by
  classical
  exact if D.basis 0 = gibbsConstant (show 1 ≤ N by omega) β H hH 1 then D else D.negBasis

theorem normalized_basis_zero (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) :
    D.normalized.basis 0 = gibbsConstant (show 1 ≤ N by omega) β H hH 1 := by
  classical
  unfold normalized
  split_ifs with h
  · exact h
  · have hn := (D.basis_zero_eq_one_or_neg hHC).resolve_left h
    change negHilbertBasis D.basis 0 = _
    rw [negHilbertBasis_apply, hn, neg_neg]

@[simp] theorem normalized_resolventEigenvalue (D : SphericalSpectralData hN β H hH) (n : ℕ) :
    D.normalized.resolventEigenvalue n = D.resolventEigenvalue n := by
  classical
  unfold normalized
  split_ifs <;> rfl

@[simp] theorem normalized_eigenvalue (D : SphericalSpectralData hN β H hH) (n : ℕ) :
    D.normalized.eigenvalue n = D.eigenvalue n := by
  simp only [eigenvalue, normalized_resolventEigenvalue]

end SphericalSpectralData

/-- Literal normalized spectral data are obtained from the actual compact
form resolvent, with no eigenbasis or normalization supplied as a premise. -/
def normalizedSphericalSpectralData {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : SphericalSpectralData hN β H hH :=
  (sphericalSpectralData hN β H hH).normalized

theorem normalizedSphericalSpectralData_basis_zero {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) :
    (normalizedSphericalSpectralData hN β H hH.continuous).basis 0 =
      gibbsConstant (show 1 ≤ N by omega) β H hH.continuous 1 :=
  (sphericalSpectralData hN β H hH.continuous).normalized_basis_zero hH

end
end SlowEquilibration.SphericalForm
