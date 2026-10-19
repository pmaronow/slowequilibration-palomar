module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.GaussianAffineDeterminantFinite

@[expose] public section

/-! # All-N actual affine Gaussian determinant moments -/

namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

/-- The fixed coefficient space in the genuine Gaussian covariance
factorization, allowing degenerate covariance as well. -/
abbrev CoefficientIndex (n : ℕ) := Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix (n+1)))

/-- Returned actual raw and clipped normalized moments, with a single
constant chosen before all ambient dimensions and matrix parameters. -/
structure UniformMomentBounds {n : ℕ}
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ (CoefficientIndex n) →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k ρ K : ℝ) : Prop where
  integrable : Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  expectation_pos : 0 < ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)
  raw_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun z => (absoluteDet C W k z /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r)
    (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  clipped_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun z => (Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r)
    (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  ordered : ∀ r : ℝ, 0 ≤ r →
    (∫ z, (absoluteDet C W k z /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)) ≤
    (∫ z, (Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  bound : ∀ r : ℝ, 0 ≤ r →
    (∫ z, (Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)) ≤ K^r*Real.exp (K*r^2)

namespace UniformMomentBounds
variable {n : ℕ} {C : GOEAsymptotics.GaussianMatrix (n+1)}
  {W : EuclideanSpace ℝ (CoefficientIndex n) →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)} {k ρ K : ℝ}

theorem raw_bound (h : UniformMomentBounds C W k ρ K) (r : ℝ) (hr : 0 ≤ r) :
    (∫ z, (absoluteDet C W k z /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)) ≤ K^r*Real.exp (K*r^2) :=
  (h.ordered r hr).trans (h.bound r hr)
end UniformMomentBounds

/-- Actual all-N determinant moments under the physical covariance scale.
The proof combines the genuine spectral large-N event with genuine Gaussian
ball estimates in the finitely many remaining matrix dimensions. -/
theorem covarianceScale_normalized_moments_all_dimensions {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N n : ℕ), n+1 ≤ N →
      ∀ (C : GOEAsymptotics.GaussianMatrix (n+1))
        (W : EuclideanSpace ℝ (CoefficientIndex n) →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)),
      (∀ i j, C i j = C j i) → (∀ z i j, W z i j = W z j i) →
      ‖W‖ ≤ Real.sqrt (2*b/N) → ‖gaussianMatrixCLM C‖ ≤ g/4 →
      ∀ k : ℝ, 2*Real.sqrt b+g ≤ k → UniformMomentBounds C W k (g/2) K := by
  let κ := 2*Real.sqrt b+g
  let σ := Real.sqrt (2*b)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hρ : 0 < g/2 := by positivity
  have hρκ : g/2 ≤ κ := by dsimp [κ]; nlinarith [Real.sqrt_nonneg b]
  obtain ⟨N₀, hlarge⟩ := eventually_atTop.mp (covarianceScale_normalized_moments_eventually hb hg)
  choose A hA hlocal using fun n : ℕ =>
    fixedDimension_normalized_moments (ι := CoefficientIndex n) n hκ hσ
  let S := Finset.sum (Finset.range N₀) A
  let K := max 2 (max (4*b/g^2) S)
  have h2K : (2:ℝ) ≤ K := le_max_left _ _
  have hMK : 4*b/g^2 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hSK : S ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, (by linarith), ?_⟩
  intro N n hN C W hC hSym hW hmean k hk
  by_cases hNN : N₀ ≤ N
  · have hd := hlarge N hNN n hN (CoefficientIndex n) C W hC hSym hW hmean k hk
    refine ⟨hd.integrable, hd.expectation_pos, hd.raw_integrable, hd.clipped_integrable, hd.ordered, ?_⟩
    intro r hr
    exact (hd.bound r hr).trans (mul_le_mul (Real.rpow_le_rpow (by norm_num) h2K hr)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hMK (sq_nonneg r)))
      (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))
  · have hn : n < N₀ := by omega
    have hnK : A n ≤ K := (Finset.single_le_sum
      (fun i _ => show 0 ≤ A i from (by linarith [hA i])) (Finset.mem_range.mpr hn)).trans hSK
    have hNp : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
    have hscale : Real.sqrt (2*b/N) ≤ σ := by
      apply Real.sqrt_le_sqrt
      exact (div_le_iff₀ hNp).mpr (by nlinarith [hb])
    have hmean' : ‖gaussianMatrixCLM C‖ ≤ κ/4 := by dsimp [κ]; nlinarith [Real.sqrt_nonneg b]
    have hd := hlocal n C W hC hSym (hW.trans hscale) hmean' k (g/2) hk hρ hρκ
    refine ⟨hd.1, hd.2.1, fun r hr => (hd.2.2 r hr).1,
      fun r hr => (hd.2.2 r hr).2.1, fun r hr => (hd.2.2 r hr).2.2.1, ?_⟩
    intro r hr
    exact ((hd.2.2 r hr).2.2.2).trans
      (mul_le_mul (Real.rpow_le_rpow (by linarith [hA n]) hnK hr)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnK (sq_nonneg r)))
        (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))

end
end SlowEquilibration.GaussianAffineDeterminant
