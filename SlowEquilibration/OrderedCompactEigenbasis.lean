-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CompactEigenbasis
public import SlowEquilibration.PositiveWeightOrdering

@[expose] public section

namespace SlowEquilibration.CompactEigenbasis

open MeasureTheory Filter Module Set Function
open scoped Topology InnerProductSpace

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- If the actual Hilbert space is not finite-dimensional, its genuine
compact spectral Hilbert basis has an infinite index. -/
theorem compactSpectralIndex_infinite (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hs : T.toLinearMap.IsSymmetric) (hInfiniteDim : ¬ FiniteDimensional ℝ H) :
    Infinite (CompactSpectralIndex T) := by
  classical
  by_contra hn
  let : Finite (CompactSpectralIndex T) := Finite.of_not_infinite hn
  let : Fintype (CompactSpectralIndex T) := Fintype.ofFinite _
  exact hInfiniteDim (Module.Finite.of_basis
    (compactSpectralBasis T hc hs).toOrthonormalBasis.toBasis)

/-- The full ordered Hilbert-basis spectral theorem for a compact strictly
positive self-adjoint contraction on an infinite-dimensional separable real
Hilbert space. The basis and the ordering are constructed, not assumed. -/
theorem exists_ordered_nat_eigenbasis [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric)
    (hp : ∀ f : H, f ≠ 0 → 0 < inner ℝ (T f) f) (hnorm : ‖T‖ ≤ 1)
    (hInfiniteDim : ¬ FiniteDimensional ℝ H) :
    ∃ b : HilbertBasis ℕ ℝ H, ∃ μ : ℕ → ℝ,
      (∀ n, 0 < μ n ∧ μ n ≤ 1) ∧ Antitone μ ∧ Tendsto μ atTop (𝓝 (0:ℝ)) ∧
      (∀ n, T (b n) = μ n • b n) ∧
      Monotone (fun n => (μ n)⁻¹-1) ∧ Tendsto (fun n => (μ n)⁻¹-1) atTop atTop := by
  classical
  let : Countable (CompactSpectralIndex T) := compactSpectralIndex_countable T hs
  let : Infinite (CompactSpectralIndex T) := compactSpectralIndex_infinite T hc hs hInfiniteDim
  have hpos (i : CompactSpectralIndex T) : 0 < i.1 :=
    (compactSpectralBasis_eigenvalue_bounds T hc hs hp hnorm i).1
  have hfinite (c : ℝ) (hc0 : 0 < c) : {i : CompactSpectralIndex T | c ≤ i.1}.Finite :=
    compactSpectralBasis_superlevel_finite T hc hs hc0
  obtain ⟨e, he⟩ := PositiveWeightOrdering.exists_antitone_enumeration
    (fun i : CompactSpectralIndex T => i.1) hpos hfinite
  let b0 := compactSpectralBasis T hc hs
  have ho : Orthonormal ℝ (fun n => b0 (e n)) := b0.orthonormal.comp e e.injective
  have hrange : Set.range (fun n => b0 (e n)) = Set.range b0 := by
    ext v
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨n, rfl⟩ := e.surjective i
      exact ⟨n, rfl⟩
  have hd : ⊤ ≤ (Submodule.span ℝ (Set.range (fun n => b0 (e n)))).topologicalClosure := by
    rw [hrange, b0.dense_span]
  let b : HilbertBasis ℕ ℝ H := HilbertBasis.mk ho hd
  have hb (n : ℕ) : b n = b0 (e n) := by simp only [b, HilbertBasis.coe_mk]
  let μ : ℕ → ℝ := fun n => (e n).1
  have hμ (n : ℕ) : 0 < μ n ∧ μ n ≤ 1 :=
    compactSpectralBasis_eigenvalue_bounds T hc hs hp hnorm (e n)
  have ht : Tendsto μ atTop (𝓝 (0:ℝ)) :=
    PositiveWeightOrdering.tendsto_zero_of_finite_superlevels
      (fun i : CompactSpectralIndex T => i.1) hpos hfinite e e.injective
  refine ⟨b, μ, hμ, he, ht, ?_, ?_, ?_⟩
  · intro n
    rw [hb]
    exact compactSpectralBasis_eigen T hc hs (e n)
  · exact PositiveWeightOrdering.generator_weights_monotone μ (fun n => (hμ n).1) he
  · exact PositiveWeightOrdering.generator_weights_tendsto_atTop μ (fun n => (hμ n).1) ht

omit [CompleteSpace H] in
/-- In any proved eigen-Hilbert basis the true operator has the convergent
ordered spectral expansion. -/
theorem ordered_basis_hasSum_operator (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
    (μ : ℕ → ℝ) (he : ∀ n, T (b n) = μ n • b n) (f : H) :
    HasSum (fun n => (μ n * inner ℝ (b n) f) • b n) (T f) := by
  have h := (b.hasSum_repr f).mapL T
  simpa only [map_smul, HilbertBasis.repr_apply_apply, he, smul_smul, mul_comm] using h

end SlowEquilibration.CompactEigenbasis
