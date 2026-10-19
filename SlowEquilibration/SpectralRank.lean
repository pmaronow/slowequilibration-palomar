-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SpectralSemigroup
public import Mathlib

@[expose] public section

namespace SlowEquilibration.SpectralRank

open Set Filter Module
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A genuine diverging eigenvalue sequence has only finitely many indices
below any real cutoff. -/
theorem cutoff_indices_finite (eigenvalue : ℕ → ℝ) (ht : Tendsto eigenvalue atTop atTop) (Λ : ℝ) :
    {j | eigenvalue j ≤ Λ}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (Λ+1)))
  apply (Finset.range N).finite_toSet.subset
  intro j hj
  change eigenvalue j ≤ Λ at hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hn
  have h := hN j (le_of_not_gt hn)
  linarith

/-- The actual positive cutoff indices; every zero mode is excluded without
assuming that the constant mode is simple. -/
noncomputable def positiveCutoffIndices (D : SpectralSemigroup.Data H)
    (ht : Tendsto D.eigenvalue atTop atTop) (Λ : ℝ) : Finset ℕ :=
  ((cutoff_indices_finite D.eigenvalue ht Λ).subset
    (show {j | 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ} ⊆ {j | D.eigenvalue j ≤ Λ}
      from fun _ hj => hj.2)).toFinset

@[simp] theorem mem_positiveCutoffIndices (D : SpectralSemigroup.Data H)
    (ht : Tendsto D.eigenvalue atTop atTop) (Λ : ℝ) (j : ℕ) :
    j ∈ positiveCutoffIndices D ht Λ ↔ 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ := by
  classical
  simp only [positiveCutoffIndices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The genuine finite-dimensional span of the indicated members of an
ordinary Hilbert basis. The ambient Hilbert space remains infinite-dimensional. -/
def basisSpan (b : HilbertBasis ℕ ℝ H) (s : Finset ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i : s => b i.val))

theorem basisSpan_finrank (b : HilbertBasis ℕ ℝ H) (s : Finset ℕ) :
    finrank ℝ (basisSpan b s) = s.card := by
  classical
  have hli : LinearIndependent ℝ (fun i : s => b i.val) :=
    b.orthonormal.linearIndependent.comp (fun i : s => i.val) Subtype.val_injective
  rw [basisSpan, finrank_span_eq_card hli, Fintype.card_coe]

/-- An ordinary Hilbert vector whose coefficients vanish outside a finite
set is its actual finite sum of those basis coefficients. -/
theorem mem_basisSpan_of_coefficients_supported (b : HilbertBasis ℕ ℝ H) (s : Finset ℕ)
    (x : H) (hz : ∀ j ∉ s, inner ℝ (b j) x = 0) : x ∈ basisSpan b s := by
  classical
  have hs := b.hasSum_repr x
  have hzero : ∀ j ∉ s, b.repr x j • b j = 0 := by
    intro j hj
    rw [HilbertBasis.repr_apply_apply, hz j hj, zero_smul]
  rw [← hs.tsum_eq, tsum_eq_sum hzero]
  apply Submodule.sum_mem
  intro j hj
  exact (basisSpan b s).smul_mem _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)

/-- The actual positive spectral projection range is exactly the span of
its genuine finite cutoff eigenvectors. -/
theorem lowSubspace_eq_basisSpan (D : SpectralSemigroup.Data H)
    (ht : Tendsto D.eigenvalue atTop atTop) (Λ : ℝ) :
    D.lowSubspace Λ = basisSpan D.basis (positiveCutoffIndices D ht Λ) := by
  classical
  apply le_antisymm
  · intro x hx
    apply mem_basisSpan_of_coefficients_supported
    intro j hj
    have hnot : ¬(0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ) := by
      simpa only [mem_positiveCutoffIndices] using hj
    exact (D.mem_lowSubspace_iff Λ x).mp hx j hnot
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (D.mem_lowSubspace_iff Λ (D.basis i.val)).mpr
    intro j hj
    have hji : j ≠ i.val := by
      intro heq
      subst j
      exact hj ((mem_positiveCutoffIndices D ht Λ i.val).mp i.property)
    exact D.basis.orthonormal.inner_eq_zero hji

/-- The true rank of the actual positive spectral projection equals the
number of positive eigenvalues below the cutoff, counted with multiplicity. -/
theorem lowSubspace_finrank (D : SpectralSemigroup.Data H)
    (ht : Tendsto D.eigenvalue atTop atTop) (Λ : ℝ) :
    finrank ℝ (D.lowSubspace Λ) = (positiveCutoffIndices D ht Λ).card := by
  rw [lowSubspace_eq_basisSpan D ht Λ]
  exact basisSpan_finrank D.basis _

/-- The actual positive cutoff range is finite-dimensional; no spectral-rank
assumption appears in this theorem. -/
theorem lowSubspace_finiteDimensional (D : SpectralSemigroup.Data H)
    (ht : Tendsto D.eigenvalue atTop atTop) (Λ : ℝ) : FiniteDimensional ℝ (D.lowSubspace Λ) := by
  rw [lowSubspace_eq_basisSpan D ht Λ, basisSpan]
  exact Module.Finite.span_of_finite _ (Set.finite_range _)

end SlowEquilibration.SpectralRank
