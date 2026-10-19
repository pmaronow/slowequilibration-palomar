module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.GOEClippedDeterminants
public import SlowEquilibration.RareEventMomentTransfer
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

/-! # Literal affine symmetric Gaussian determinant moments

The clipped logarithm and ordinary determinant are actual functions of the
original Gaussian coefficients. The clipping event is the actual largest
eigenvalue event, and all normalized moments refer to the raw determinant's
own expectation.
-/

namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory ProbabilityTheory Filter
open OAI.CriticalSK GOEAsymptotics GOEEdgeConcentration SpectralTraceLipschitz
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The actual affine random matrix, with the original Gaussian source. -/
def affineMatrix (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (g : EuclideanSpace ℝ ι) : GOEAsymptotics.GaussianMatrix (n+1) := C + W g

lemma affineMatrix_symmetric (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hW : ∀ g i j, W g i j = W g j i)
    (g : EuclideanSpace ℝ ι) : ∀ i j, affineMatrix C W g i j = affineMatrix C W g j i := by
  intro i j
  simp only [affineMatrix, PiLp.add_apply, hC i j, hW g i j]

/-- Literal sum of clipped logarithms of the actual affine spectrum. -/
def clippedTrace (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k ρ : ℝ) (g : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, clippedLog k ρ (matrixOrderedEigenvalues (affineMatrix C W g) i)

/-- Literal raw absolute determinant of the actual affine matrix. -/
def absoluteDet (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k : ℝ) (g : EuclideanSpace ℝ ι) : ℝ :=
  |(k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - gaussianToMatrix (affineMatrix C W g)).det|

lemma absoluteDet_eq_prod (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hW : ∀ g i j, W g i j = W g j i)
    (k : ℝ) (g : EuclideanSpace ℝ ι) :
    absoluteDet C W k g = ∏ i, |k - matrixOrderedEigenvalues (affineMatrix C W g) i| := by
  rw [absoluteDet, GOEClippedDeterminants.shifted_det_eq_prod k _
    (affineMatrix_symmetric C W hC hW g), Finset.abs_prod]

lemma exp_clippedTrace (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (g : EuclideanSpace ℝ ι) :
    Real.exp (clippedTrace C W k ρ g) =
      ∏ i, max |k - matrixOrderedEigenvalues (affineMatrix C W g) i| ρ := by
  unfold clippedTrace clippedLog
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (hρ.trans_le (le_max_right _ _))

lemma absoluteDet_nonneg (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k : ℝ) (g : EuclideanSpace ℝ ι) : 0 ≤ absoluteDet C W k g := abs_nonneg _

lemma absoluteDet_le_exp_clippedTrace (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hW : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (g : EuclideanSpace ℝ ι) :
    absoluteDet C W k g ≤ Real.exp (clippedTrace C W k ρ g) := by
  rw [absoluteDet_eq_prod C W hC hW, exp_clippedTrace C W k hρ]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => le_max_left _ _)

/-- The top actual eigenvalue decides the literal clipping event. -/
def gapBad (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k ρ : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {g | k-ρ < matrixOrderedEigenvalues (affineMatrix C W g) 0}

lemma eigenvalue_le_upper (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    matrixOrderedEigenvalues A i ≤ matrixOrderedEigenvalues A 0 := by
  rw [matrixOrderedEigenvalues_eq A hA]
  exact (gaussianMatrixCLM_symmetric A hA).eigenvalues_antitone _ (Fin.zero_le i)

lemma absoluteDet_eq_exp_clippedTrace_of_not_bad
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hW : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (g : EuclideanSpace ℝ ι)
    (hg : g ∉ gapBad C W k ρ) :
    absoluteDet C W k g = Real.exp (clippedTrace C W k ρ g) := by
  rw [absoluteDet_eq_prod C W hC hW, exp_clippedTrace C W k hρ]
  apply Finset.prod_congr rfl
  intro i _
  have hi := (eigenvalue_le_upper _ (affineMatrix_symmetric C W hC hW g) i).trans
    (le_of_not_gt hg)
  exact (max_eq_left ((by linarith : ρ ≤ k - matrixOrderedEigenvalues (affineMatrix C W g) i).trans
    (le_abs_self _))).symm

lemma absoluteDet_eq_exp_clippedTrace_of_upper_le
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hW : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (g : EuclideanSpace ℝ ι)
    (hg : matrixOrderedEigenvalues (affineMatrix C W g) 0 ≤ k-ρ) :
    absoluteDet C W k g = Real.exp (clippedTrace C W k ρ g) :=
  absoluteDet_eq_exp_clippedTrace_of_not_bad C W hC hW k hρ g (not_lt_of_ge hg)

/-- True Lipschitz constant from Frobenius covariance domination. -/
def clippedLip (n : ℕ) (σ ρ : ℝ) : ℝ := Real.sqrt (n+1 : ℝ) * σ / ρ

def clippedVariance (n : ℕ) (σ ρ : ℝ) : ℝ := (n+1 : ℝ)*σ^2/ρ^2

lemma clippedLip_positive (n : ℕ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) :
    0 < clippedLip n σ ρ := by
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) hσ) hρ

lemma clippedLip_square (n : ℕ) {σ ρ : ℝ} :
    (clippedLip n σ ρ)^2 = clippedVariance n σ ρ := by
  unfold clippedLip clippedVariance
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]

lemma clippedTrace_lipschitz (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ) :
    LipschitzWith (clippedLip n σ ρ).toNNReal (clippedTrace C W k ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  change |clippedTrace C W k ρ g - clippedTrace C W k ρ h| ≤ _
  have htrace := spectral_trace_difference (affineMatrix C W g) (affineMatrix C W h)
    (affineMatrix_symmetric C W hC hSym g) (affineMatrix_symmetric C W hC hSym h)
    (clippedLog k ρ) (clippedLog_lipschitz k hρ)
  have hdiff : affineMatrix C W g - affineMatrix C W h = W (g-h) := by
    rw [affineMatrix, affineMatrix, add_sub_add_left_eq_sub, map_sub]
  rw [hdiff] at htrace
  have hn : ‖W (g-h)‖ ≤ σ*‖g-h‖ :=
    (W.le_opNorm _).trans (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
  have hh := htrace.trans (mul_le_mul_of_nonneg_left hn (by positivity))
  rw [Real.coe_toNNReal _ (clippedLip_positive n hσ hρ).le]
  change |clippedTrace C W k ρ g-clippedTrace C W k ρ h| ≤
    Real.sqrt ((n+1:ℕ):ℝ) * (1/ρ) * (σ*‖g-h‖) at hh
  simpa only [clippedLip, Nat.cast_add, Nat.cast_one, dist_eq_norm, div_eq_mul_inv, one_mul,
    mul_assoc, mul_left_comm, mul_comm] using hh

/-- Sharp original-coefficient Gaussian MGF for the literal affine clipped logdet. -/
theorem clippedTrace_centered_subGaussian (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ) :
    HasSubgaussianMGF (fun g => clippedTrace C W k ρ g -
      ∫ h, clippedTrace C W k ρ h ∂SYK.standardGaussianMeasureOnEuclidean ι)
      (clippedVariance n σ ρ).toNNReal (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have h := SYK.product_standardGaussian_hasSubgaussianMGF
    (clippedTrace C W k ρ) (clippedLip n σ ρ) (clippedLip_positive n hσ hρ)
    (clippedTrace_lipschitz C W hC hSym k hσ hρ hW)
  rw [clippedLip_square] at h
  exact h

lemma clippedTrace_integrable (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ) :
    Integrable (clippedTrace C W k ρ) (SYK.standardGaussianMeasureOnEuclidean ι) :=
  by
    have hsg := clippedTrace_centered_subGaussian C W hC hSym k hσ hρ hW
    have hi := hsg.integrable.add (integrable_const
      (∫ h, clippedTrace C W k ρ h ∂SYK.standardGaussianMeasureOnEuclidean ι))
    convert hi using 1
    funext g
    change clippedTrace C W k ρ g = clippedTrace C W k ρ g - _ + _
    ring


lemma gapBad_measurable (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i) (k ρ : ℝ) :
    MeasurableSet (gapBad C W k ρ) := by
  have ht : LipschitzWith ‖W‖₊ (fun g => matrixOrderedEigenvalues (affineMatrix C W g) 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro g h
    change |matrixOrderedEigenvalues (affineMatrix C W g) 0 -
      matrixOrderedEigenvalues (affineMatrix C W h) 0| ≤ ‖W‖*‖g-h‖
    have hb := symmetric_gaussian_eigenvalue_lipschitz _ _
      (affineMatrix_symmetric C W hC hSym g) (affineMatrix_symmetric C W hC hSym h) 0
    have he : affineMatrix C W g-affineMatrix C W h = W (g-h) := by
      rw [affineMatrix, affineMatrix, add_sub_add_left_eq_sub, map_sub]
    rw [he] at hb
    exact hb.trans (W.le_opNorm _)
  exact measurableSet_lt measurable_const ht.continuous.measurable

lemma absoluteDet_measurable (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) (k : ℝ) :
    Measurable (absoluteDet C W k) := by
  have ha : Measurable (affineMatrix C W) := (continuous_const.add W.continuous).measurable
  have hm := (gaussianToMatrix_measurable (n+1)).comp ha
  unfold absoluteDet
  fun_prop

/-- Actual raw-determinant moment transfer using its true top-eigenvalue
clipping event. The event smallness is the explicit finite-dimensional
quantity supplied by the separately proved sharp spectral-edge theorem. -/
theorem raw_normalized_moments (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ)
    (hsmall : Real.exp (clippedVariance n σ ρ) * Real.sqrt
      ((SYK.standardGaussianMeasureOnEuclidean ι).real (gapBad C W k ρ)) ≤ 1/2) :
    Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean ι) ∧
    Real.exp (∫ g, clippedTrace C W k ρ g ∂SYK.standardGaussianMeasureOnEuclidean ι)/2 ≤
      ∫ g, absoluteDet C W k g ∂SYK.standardGaussianMeasureOnEuclidean ι ∧
    0 < ∫ g, absoluteDet C W k g ∂SYK.standardGaussianMeasureOnEuclidean ι ∧
    ∀ r : ℝ, 0 ≤ r →
      Integrable (fun g => (absoluteDet C W k g /
        (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
        (SYK.standardGaussianMeasureOnEuclidean ι) ∧
      (∫ g, (absoluteDet C W k g /
        (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
        (2:ℝ)^r * Real.exp (clippedVariance n σ ρ*r^2/2) := by
  have hv : 0 ≤ clippedVariance n σ ρ := by unfold clippedVariance; positivity
  have h := RareEventMomentTransfer.normalized_dominated_exponential_moments
    (clippedTrace C W k ρ) (absoluteDet C W k)
    (clippedTrace_integrable C W hC hSym k hσ hρ hW)
    (absoluteDet_measurable C W k).aemeasurable (clippedVariance n σ ρ).toNNReal
    (clippedTrace_centered_subGaussian C W hC hSym k hσ hρ hW)
    (gapBad C W k ρ) (gapBad_measurable C W hC hSym k ρ)
    (ae_of_all _ (fun g => ⟨absoluteDet_nonneg C W k g,
      absoluteDet_le_exp_clippedTrace C W hC hSym k hρ g⟩))
    (ae_of_all _ (fun g hg => absoluteDet_eq_exp_clippedTrace_of_not_bad C W hC hSym k hρ g hg))
    (by rw [Real.coe_toNNReal _ hv]; exact hsmall)
  simpa only [Real.coe_toNNReal _ hv] using h

/-- The clipped exponential is normalized by the raw determinant's actual
own expectation, with the same sharp bound and literal clipping event. -/
theorem clipped_over_raw_normalized_moments
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ)
    (hsmall : Real.exp (clippedVariance n σ ρ) * Real.sqrt
      ((SYK.standardGaussianMeasureOnEuclidean ι).real (gapBad C W k ρ)) ≤ 1/2)
    (r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun g => (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
      (SYK.standardGaussianMeasureOnEuclidean ι) ∧
    (∫ g, (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      (2:ℝ)^r * Real.exp (clippedVariance n σ ρ*r^2/2) := by
  have hv : 0 ≤ clippedVariance n σ ρ := by unfold clippedVariance; positivity
  have h := RareEventMomentTransfer.normalized_upper_exponential_moments
    (clippedTrace C W k ρ) (absoluteDet C W k)
    (clippedTrace_integrable C W hC hSym k hσ hρ hW)
    (absoluteDet_measurable C W k).aemeasurable (clippedVariance n σ ρ).toNNReal
    (clippedTrace_centered_subGaussian C W hC hSym k hσ hρ hW)
    (gapBad C W k ρ) (gapBad_measurable C W hC hSym k ρ)
    (ae_of_all _ (fun g => ⟨absoluteDet_nonneg C W k g,
      absoluteDet_le_exp_clippedTrace C W hC hSym k hρ g⟩))
    (ae_of_all _ (fun g hg => absoluteDet_eq_exp_clippedTrace_of_not_bad C W hC hSym k hρ g hg))
    (by rw [Real.coe_toNNReal _ hv]; exact hsmall) r hr
  simpa only [Real.coe_toNNReal _ hv] using h

/-- The actual raw and clipped normalized moments have their literal
pointwise domination order; no raw moment bound is an input. -/
theorem raw_normalized_le_clipped_normalized
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ g i j, W g i j = W g j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ)
    (hsmall : Real.exp (clippedVariance n σ ρ) * Real.sqrt
      ((SYK.standardGaussianMeasureOnEuclidean ι).real (gapBad C W k ρ)) ≤ 1/2)
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ g, (absoluteDet C W k g /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    (∫ g, (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hraw := raw_normalized_moments C W hC hSym k hσ hρ hW hsmall
  have hclip := clipped_over_raw_normalized_moments C W hC hSym k hσ hρ hW hsmall r hr
  apply integral_mono (hraw.2.2.2 r hr).1 hclip.1
  intro g
  have hpos := hraw.2.2.1
  apply Real.rpow_le_rpow (div_nonneg (absoluteDet_nonneg C W k g) hpos.le) _ hr
  exact div_le_div_of_nonneg_right (absoluteDet_le_exp_clippedTrace C W hC hSym k hρ g) hpos.le

end
end SlowEquilibration.GaussianAffineDeterminant
