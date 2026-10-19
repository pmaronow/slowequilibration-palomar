module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.GaussianAffineDeterminant
public import SlowEquilibration.GaussianDominatedEdge

@[expose] public section

/-! # Uniform large-N moments of actual covariance-dominated affine determinants -/

namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
universe u

lemma covarianceScale_variance_le {n N : ℕ} (hN : n+1 ≤ N)
    {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    clippedVariance n (Real.sqrt (2*b/N)) (g/2) ≤ 8*b/g^2 := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hnN : (n+1:ℝ) ≤ N := by exact_mod_cast hN
  unfold clippedVariance
  rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*b/N)]
  have hmult := mul_le_mul_of_nonneg_right hnN (show 0 ≤ 2*b/(N:ℝ) by positivity)
  have hright : (N:ℝ)*(2*b/(N:ℝ)) = 2*b := by field_simp
  rw [hright] at hmult
  have hh := div_le_div_of_nonneg_right hmult (show 0 ≤ (g/2)^2 by positivity)
  exact hh.trans_eq (by field_simp; ring)

/-- Literal true clipping failure is contained in the proved affine
spectral-edge event, so its probability has the source exponential rate. -/
lemma gapBad_probability_covarianceScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n N : ℕ} (hN : n+1 ≤ N) {b g : ℝ} (hb : 0 < b) (hg : 0 < g)
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) (hmean : ‖gaussianMatrixCLM C‖ ≤ g/4)
    (k : ℝ) (hk : 2*Real.sqrt b+g ≤ k) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real (gapBad C W k (g/2)) ≤
      Real.exp (-(N:ℝ)*g^2/(64*b)) := by
  refine (measureReal_mono (fun z hz => ?_)).trans
    (GaussianDominatedEdge.affine_fixed_gap_probability W hSym C hC hN hb hg hW hmean)
  refine ⟨0, ?_⟩
  change k-g/2 < matrixOrderedEigenvalues (C+W z) 0 at hz
  linarith

lemma scalar_clipping_smallness_eventually {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (8*b/g^2)*Real.sqrt (Real.exp (-(N:ℝ)*g^2/(64*b))) ≤ 1/2 := by
  have ha : 0 < g^2/(64*b) := by positivity
  have harg : Tendsto (fun N : ℕ => (N:ℝ)*(g^2/(64*b))) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const' ha
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ)*g^2/(64*b))) atTop (𝓝 (0:ℝ)) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp harg using 1
    funext N
    congr 1
    ring
  have hs := ht.sqrt.const_mul (Real.exp (8*b/g^2))
  simp only [Real.sqrt_zero, mul_zero] at hs
  exact (hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))).mono (fun N h => h.le)

/-- The ambient threshold is chosen before the original Gaussian source,
matrix dimension, deterministic shift and spectral shift. -/
theorem clipping_smallness_covarianceScale_eventually {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n+1 ≤ N →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
        (C : GOEAsymptotics.GaussianMatrix (n+1))
        (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)),
      (∀ i j, C i j = C j i) → (∀ z i j, W z i j = W z j i) →
      ‖W‖ ≤ Real.sqrt (2*b/N) → ‖gaussianMatrixCLM C‖ ≤ g/4 →
      ∀ k : ℝ, 2*Real.sqrt b+g ≤ k →
      Real.exp (clippedVariance n (Real.sqrt (2*b/N)) (g/2))*Real.sqrt
        ((SYK.standardGaussianMeasureOnEuclidean ι).real (gapBad C W k (g/2))) ≤ 1/2 := by
  filter_upwards [scalar_clipping_smallness_eventually hb hg] with N hsmall
  intro n hN ι _ _ C W hC hSym hW hmean k hk
  have hv := covarianceScale_variance_le hN hb hg
  have hp := gapBad_probability_covarianceScale hN hb hg C W hC hSym hW hmean k hk
  exact (mul_le_mul (Real.exp_le_exp.mpr hv) (Real.sqrt_le_sqrt hp)
    (Real.sqrt_nonneg _) (Real.exp_pos _).le).trans hsmall

/-- Actual estimates returned by the proved affine determinant theorem.
Both moments use the raw determinant's own expectation. -/
structure NormalizedMomentBounds {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) (k ρ M : ℝ) : Prop where
  integrable : Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean ι)
  expectation_pos : 0 < ∫ g, absoluteDet C W k g ∂SYK.standardGaussianMeasureOnEuclidean ι
  raw_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun g => (absoluteDet C W k g /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
    (SYK.standardGaussianMeasureOnEuclidean ι)
  clipped_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun g => (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
    (SYK.standardGaussianMeasureOnEuclidean ι)
  ordered : ∀ r : ℝ, 0 ≤ r →
    (∫ g, (absoluteDet C W k g /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    (∫ g, (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι)
  bound : ∀ r : ℝ, 0 ≤ r →
    (∫ g, (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ (2:ℝ)^r*Real.exp (M*r^2)

namespace NormalizedMomentBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
  {C : GOEAsymptotics.GaussianMatrix (n+1)}
  {W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)} {k ρ M : ℝ}

theorem raw_bound (h : NormalizedMomentBounds C W k ρ M) (r : ℝ) (hr : 0 ≤ r) :
    (∫ g, (absoluteDet C W k g /
      (∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ (2:ℝ)^r*Real.exp (M*r^2) :=
  (h.ordered r hr).trans (h.bound r hr)

end NormalizedMomentBounds

/-- Genuine uniform source determinant moments, allowing arbitrary original
Gaussian source dimension, arbitrary symmetric covariance-dominated noise,
and every matrix dimension not exceeding the ambient dimension. -/
theorem covarianceScale_normalized_moments_eventually {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n+1 ≤ N →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
        (C : GOEAsymptotics.GaussianMatrix (n+1))
        (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)),
      (∀ i j, C i j = C j i) → (∀ z i j, W z i j = W z j i) →
      ‖W‖ ≤ Real.sqrt (2*b/N) → ‖gaussianMatrixCLM C‖ ≤ g/4 →
      ∀ k : ℝ, 2*Real.sqrt b+g ≤ k → NormalizedMomentBounds C W k (g/2) (4*b/g^2) := by
  filter_upwards [clipping_smallness_covarianceScale_eventually hb hg] with N hsmall
  intro n hN ι _ _ C W hC hSym hW hmean k hk
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hσ : 0 < Real.sqrt (2*b/N) := Real.sqrt_pos.mpr (by positivity)
  have hρ : 0 < g/2 := by positivity
  have hs := hsmall n hN ι C W hC hSym hW hmean k hk
  have hraw := raw_normalized_moments C W hC hSym k hσ hρ hW hs
  refine ⟨hraw.1, hraw.2.2.1, fun r hr => (hraw.2.2.2 r hr).1,
    fun r hr => (clipped_over_raw_normalized_moments C W hC hSym k hσ hρ hW hs r hr).1,
    fun r hr => raw_normalized_le_clipped_normalized C W hC hSym k hσ hρ hW hs r hr, ?_⟩
  intro r hr
  have hbnd := (clipped_over_raw_normalized_moments C W hC hSym k hσ hρ hW hs r hr).2
  refine hbnd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by norm_num) _))
  have hv := mul_le_mul_of_nonneg_right (covarianceScale_variance_le hN hb hg) (sq_nonneg r)
  calc
    _ ≤ (8*b/g^2*r^2)/2 := div_le_div_of_nonneg_right hv (by norm_num)
    _ = _ := by ring

end
end SlowEquilibration.GaussianAffineDeterminant
