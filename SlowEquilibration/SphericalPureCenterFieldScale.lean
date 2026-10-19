-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureConditionalPointMean

@[expose] public section

/-! Pathwise homogeneity identifies the actual pure center field with the
original physical Hamiltonian times `Q^(p/2)`. -/

namespace SlowEquilibration.SphericalPureCenterFieldScale
noncomputable section
open SphericalModel SphericalGaussianJet
set_option autoImplicit false

theorem pure_field_spatial_smul
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (N : ℕ) (J : Disorder N (FiniteMixture.pure p hp alpha halpha).maxDegree)
    (w : Vector N) (a : ℝ) :
    field (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) J (a • w) =
      a^p*field (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) J w := by
  let μ := FiniteMixture.pure p hp alpha halpha
  unfold field
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  unfold blockField
  rw [pure_spatial_smul]
  by_cases hdp : d.val.val = p
  · rw [congrArg (fun k : ℕ => a^k) hdp]
    ring
  · have hz : mixtureCoefficients μ d = 0 := by
      simp [mixtureCoefficients,μ,FiniteMixture.pure,hdp]
    simp [hz,μ]

/-- The source's `H_Q` and original `H_N` are the same realized pure tensor
field at rescaled radius, with the exact positive scalar factor. -/
theorem pure_center_field_eq_original_scale
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (N : ℕ) (J : Disorder N (FiniteMixture.pure p hp alpha halpha).maxDegree)
    (w : Vector N) :
    field (centerCoefficients (mixtureCoefficients
      (FiniteMixture.pure p hp alpha halpha)) Q) J w =
      (Real.sqrt Q)^p *
        field (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) J w := by
  rw [field_center_scale _ (mixtureCoefficients_nonnegative _) hQ]
  exact pure_field_spatial_smul p hp alpha halpha N J w (Real.sqrt Q)

end
end SlowEquilibration.SphericalPureCenterFieldScale
