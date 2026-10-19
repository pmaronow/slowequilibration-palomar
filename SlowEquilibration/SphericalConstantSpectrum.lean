module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalSpectral

@[expose] public section

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open Set MeasureTheory Filter
open SphericalModel SphericalAging.HardSphereDynamics
open scoped InnerProductSpace Topology

namespace SphericalSpectralData
variable {N : ℕ} {hN : 2 ≤ N} {β : ℝ} {H : Vector N → ℝ} {hH : Continuous H}

/-- Constants have actual resolvent eigenvalue one in every constructed
ordered spherical basis. -/
theorem constant_coefficient_equation (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (n : ℕ) :
    D.resolventEigenvalue n *
      D.basis.repr (gibbsConstant (show 1 ≤ N by omega) β H hH 1) n =
    D.basis.repr (gibbsConstant (show 1 ≤ N by omega) β H hH 1) n := by
  have hs := sphericalL2Resolvent_symmetric (show 1 ≤ N by omega) β H hH
    (D.basis n) (gibbsConstant (show 1 ≤ N by omega) β H hH 1)
  change inner ℝ (sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis n))
    (gibbsConstant (show 1 ≤ N by omega) β H hH 1) =
    inner ℝ (D.basis n) (sphericalL2Resolvent (show 1 ≤ N by omega) β H hH
      (gibbsConstant (show 1 ≤ N by omega) β H hH 1)) at hs
  rw [D.eigen, sphericalL2Resolvent_constant (show 1 ≤ N by omega) β H hHC,
    real_inner_smul_left] at hs
  simpa only [HilbertBasis.repr_apply_apply] using hs

/-- The top actual spherical resolvent eigenvalue is exactly one, derived
from the true constant eigenvector and the true ordered complete basis. -/
theorem resolventEigenvalue_zero (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) : D.resolventEigenvalue 0 = 1 := by
  classical
  let c := gibbsConstant (show 1 ≤ N by omega) β H hH 1
  have hc : c ≠ 0 := by
    intro hz
    have hh := gibbsConstant_one_norm (show 1 ≤ N by omega) β H hH
    change ‖c‖ = 1 at hh
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hex : ∃ n, D.basis.repr c n ≠ 0 := by
    by_contra hn
    have hz : ∀ n, D.basis.repr c n = 0 := by simpa only [not_exists, not_not] using hn
    apply hc
    apply D.basis.repr.injective
    apply lp.ext
    funext n
    simp only [hz, map_zero, lp.coeFn_zero, Pi.zero_apply]
  obtain ⟨n, hn⟩ := hex
  have he := D.constant_coefficient_equation hHC n
  change D.resolventEigenvalue n * D.basis.repr c n = D.basis.repr c n at he
  have hμ : D.resolventEigenvalue n = 1 := (mul_right_cancel₀ hn) (he.trans (one_mul _).symm)
  apply le_antisymm (D.bounds 0).2
  rw [← hμ]
  exact D.antitone (Nat.zero_le n)

/-- The bottom actual spherical generator eigenvalue is exactly zero. -/
theorem eigenvalue_zero (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) : D.eigenvalue 0 = 0 := by
  rw [eigenvalue, D.resolventEigenvalue_zero hHC, inv_one, sub_self]

/-- Every true positive generator mode is orthogonal to actual constants. -/
theorem positive_mode_orthogonal_constant (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (n : ℕ) (hn : 0 < D.eigenvalue n) :
    inner ℝ (D.basis n) (gibbsConstant (show 1 ≤ N by omega) β H hH 1) = 0 := by
  have he := D.constant_coefficient_equation hHC n
  rw [HilbertBasis.repr_apply_apply] at he
  have hμ : D.resolventEigenvalue n ≠ 1 := by
    intro hh
    have hz : D.eigenvalue n = 0 := by rw [eigenvalue, hh, inv_one, sub_self]
    exact (ne_of_gt hn) hz
  have hm : (D.resolventEigenvalue n - 1) *
      inner ℝ (D.basis n) (gibbsConstant (show 1 ≤ N by omega) β H hH 1) = 0 := by
    linarith
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hμ)

end SphericalSpectralData
end
end SlowEquilibration.SphericalForm
