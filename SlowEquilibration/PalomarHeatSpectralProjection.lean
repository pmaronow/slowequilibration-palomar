-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SpectralRank

@[expose] public section

namespace SlowEquilibration.PalomarHeatSpectralProjection

open Set Filter
open scoped Topology InnerProductSpace NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A heat eigenfunction has no spectral coefficients at a different eigenvalue.
The heat equation at time one already identifies its spectral support. -/
theorem coefficient_eq_zero_of_heatEigenfunction (D : SpectralSemigroup.Data H)
    {lam : ℝ} {u : H}
    (hu : ∀ t : ℝ≥0, D.P t u = Real.exp (-(t : ℝ) * lam) • u)
    (j : ℕ) (hj : D.eigenvalue j ≠ lam) : D.coefficient u j = 0 := by
  have h := congrArg (fun x => D.coefficient x j) (hu 1)
  change D.coefficient (D.P 1 u) j =
    D.coefficient (Real.exp (-(1 : ℝ≥0) * lam) • u) j at h
  rw [D.coefficient_P] at h
  have hmul : Real.exp (-D.eigenvalue j) * D.coefficient u j =
      Real.exp (-lam) * D.coefficient u j := by
    simpa only [NNReal.coe_one,
      neg_one_mul, SpectralSemigroup.Data.coefficient, inner_smul_right] using h
  by_contra hc
  have he : Real.exp (-D.eigenvalue j) = Real.exp (-lam) := mul_right_cancel₀ hc hmul
  exact hj (neg_injective (Real.exp_injective he))

/-- Every member of the diagonal Hilbert basis is a heat eigenfunction. -/
theorem basis_heatEigenfunction (D : SpectralSemigroup.Data H) (j : ℕ) :
    ∀ t : ℝ≥0, D.P t (D.basis j) =
      Real.exp (-(t : ℝ) * D.eigenvalue j) • D.basis j := by
  intro t
  apply D.coefficient_injective
  intro k
  rw [D.coefficient_P]
  change Real.exp (-(t : ℝ) * D.eigenvalue k) *
      inner ℝ (D.basis k) (D.basis j) =
    inner ℝ (D.basis k) (Real.exp (-(t : ℝ) * D.eigenvalue j) • D.basis j)
  rw [inner_smul_right]
  by_cases hkj : k = j
  · subst k
    rfl
  · rw [D.basis.orthonormal.inner_eq_zero hkj]
    simp

/-- The cutoff range is closed because the cutoff is a continuous idempotent. -/
theorem lowSubspace_isClosed (D : SpectralSemigroup.Data H) (Λ : ℝ) :
    IsClosed (D.lowSubspace Λ : Set H) := by
  change IsClosed ((D.cutoff Λ).range : Set H)
  apply ContinuousLinearMap.IsIdempotentElem.isClosed_range
  ext x
  exact D.cutoff_idempotent Λ x

/-- The diagonal positive cutoff space agrees with the closed span of all
positive heat eigenfunctions whose eigenvalues are at most the cutoff. -/
theorem lowSubspace_eq_closedSpan_heatEigenfunctions [CompleteSpace H]
    (D : SpectralSemigroup.Data H) (ht : Tendsto D.eigenvalue atTop atTop) (Λ : ℝ) :
    D.lowSubspace Λ =
      (Submodule.span ℝ {u | ∃ lam : ℝ, 0 < lam ∧ lam ≤ Λ ∧
        ∀ t : ℝ≥0, D.P t u = Real.exp (-(t : ℝ) * lam) • u}).topologicalClosure := by
  apply le_antisymm
  · rw [SpectralRank.lowSubspace_eq_basisSpan D ht Λ, SpectralRank.basisSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    have hi := (SpectralRank.mem_positiveCutoffIndices D ht Λ i.val).mp i.property
    exact ⟨D.eigenvalue i.val, hi.1, hi.2, basis_heatEigenfunction D i.val⟩
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro u ⟨lam, hlam, hΛ, hu⟩
      apply (D.mem_lowSubspace_iff Λ u).mpr
      intro j hj
      apply coefficient_eq_zero_of_heatEigenfunction D hu j
      intro h
      exact hj (h ▸ ⟨hlam, hΛ⟩)
    · exact lowSubspace_isClosed D Λ

end SlowEquilibration.PalomarHeatSpectralProjection
