module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.GaussianAffineDeterminantUniform
public import SlowEquilibration.GaussianDensity
public import SlowEquilibration.GaussianNormMean

@[expose] public section

/-! # Genuine Gaussian-ball bounds for the remaining finite dimensions -/

namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Set MeasureTheory ProbabilityTheory Filter Metric
open OAI.CriticalSK GOEAsymptotics SpectralTraceLipschitz
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma eigenvalue_abs_le_operator_norm (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    |matrixOrderedEigenvalues A i| ≤ ‖gaussianMatrixCLM A‖ := by
  rw [matrixOrderedEigenvalues_eq A hA]
  let h := gaussianMatrixCLM_symmetric A hA
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := h.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := h.eigenvectorBasis hn |>.norm_eq_one i
  have he : gaussianMatrixCLM A v = h.eigenvalues hn i • v := h.apply_eigenvectorBasis hn i
  have hh := (gaussianMatrixCLM A).le_opNorm v
  rw [he, norm_smul, Real.norm_eq_abs, hv, mul_one, mul_one] at hh
  exact hh

lemma affine_eigenvalue_abs_le (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {σ : ℝ} (hW : ‖W‖ ≤ σ) (z : EuclideanSpace ℝ ι) (i : Fin (n+1)) :
    |matrixOrderedEigenvalues (affineMatrix C W z) i| ≤ ‖gaussianMatrixCLM C‖ + σ*‖z‖ := by
  have he : gaussianMatrixCLM (affineMatrix C W z) = gaussianMatrixCLM C + gaussianMatrixCLM (W z) :=
    (gaussianMatrixToCLM (n+1)).map_add C (W z)
  calc
    _ ≤ ‖gaussianMatrixCLM (affineMatrix C W z)‖ :=
      eigenvalue_abs_le_operator_norm _ (affineMatrix_symmetric C W hC hSym z) i
    _ ≤ ‖gaussianMatrixCLM C‖ + ‖gaussianMatrixCLM (W z)‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl ((GOEEdgeConcentration.gaussianMatrixCLM_norm_le (W z)).trans
      ((W.le_opNorm z).trans (mul_le_mul_of_nonneg_right hW (norm_nonneg z))))

/-- Actual standard Gaussian norm balls have positive probability,
including the zero-dimensional coefficient space. -/
lemma gaussian_closedBall_real_pos {a : ℝ} (ha : 0 < a) :
    0 < (SYK.standardGaussianMeasureOnEuclidean ι).real (closedBall (0 : EuclideanSpace ℝ ι) a) := by
  have hμ : SYK.standardGaussianMeasureOnEuclidean ι = stdGaussian (EuclideanSpace ℝ ι) := by
    rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  have hpos : 0 < volume (closedBall (0 : EuclideanSpace ℝ ι) a) :=
    (isOpen_ball.measure_pos volume (nonempty_ball.mpr ha)).trans_le
      (measure_mono ball_subset_closedBall)
  have hs : {z : EuclideanSpace ℝ ι | ENNReal.ofReal (GaussianDensity.density z) ≠ 0} = univ := by
    ext z
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (GaussianDensity.density_pos z)).ne'
  have hne : stdGaussian (EuclideanSpace ℝ ι) (closedBall (0 : EuclideanSpace ℝ ι) a) ≠ 0 := by
    rw [GaussianDensity.stdGaussian_eq_withDensity]
    intro hz
    have hh := (withDensity_apply_eq_zero
      GaussianDensity.density_continuous.measurable.ennreal_ofReal).mp hz
    rw [hs, univ_inter] at hh
    exact hpos.ne' hh

  rw [hμ]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

/-- A literal Gaussian norm ball gives a uniform positive raw determinant
lower bound in every fixed source and matrix dimension. -/
lemma absoluteDet_lower_on_ball (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hW : ‖W‖ ≤ σ)
    (hmean : ‖gaussianMatrixCLM C‖ ≤ κ/4) {k : ℝ} (hk : κ ≤ k)
    (z : EuclideanSpace ℝ ι) (hz : z ∈ closedBall 0 (κ/(4*σ))) :
    (k/2)^(n+1) ≤ absoluteDet C W k z := by
  have hkp : 0 < k := hκ.trans_le hk
  have hz' : ‖z‖ ≤ κ/(4*σ) := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hnoise : σ*‖z‖ ≤ κ/4 := by
    have hh := mul_le_mul_of_nonneg_left hz' hσ.le
    exact hh.trans_eq (by field_simp)
  rw [absoluteDet_eq_prod C W hC hSym]
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun _ : Fin (n+1) => k/2)
    (g := fun i => |k-matrixOrderedEigenvalues (affineMatrix C W z) i|)
    (fun _ _ => by positivity) (fun i _ => by
      have hi := le_abs_self (matrixOrderedEigenvalues (affineMatrix C W z) i)
      have hb := affine_eigenvalue_abs_le C W hC hSym hW z i
      exact (by linarith : k/2 ≤ k-matrixOrderedEigenvalues (affineMatrix C W z) i).trans (le_abs_self _))
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp

/-- Both actual clipping and ordinary determinant admit a literal
Gaussian norm exponential majorant, uniformly in the unbounded shift k. -/
lemma clippedTrace_upper_norm (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {κ σ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ) (hρκ : ρ ≤ κ)
    (hW : ‖W‖ ≤ σ) (hmean : ‖gaussianMatrixCLM C‖ ≤ κ/4)
    {k : ℝ} (hk : κ ≤ k) (z : EuclideanSpace ℝ ι) :
    clippedTrace C W k ρ z ≤ (n+1:ℝ)*Real.log k +
      (n+1:ℝ)/4 + ((n+1:ℝ)*σ/κ)*‖z‖ := by
  have hkp : 0 < k := hκ.trans_le hk
  have hq : 0 ≤ 1/4+(σ/κ)*‖z‖ := by positivity
  have hfactor (i : Fin (n+1)) :
      max |k-matrixOrderedEigenvalues (affineMatrix C W z) i| ρ ≤
        k*(1+(1/4+(σ/κ)*‖z‖)) := by
    apply max_le
    · have hEig := affine_eigenvalue_abs_le C W hC hSym hW z i
      have hab := abs_sub k (matrixOrderedEigenvalues (affineMatrix C W z) i)
      rw [abs_of_pos hkp] at hab
      have hscale : σ*‖z‖ ≤ k*((σ/κ)*‖z‖) := by
        have hm := mul_le_mul_of_nonneg_right hk (show 0 ≤ (σ/κ)*‖z‖ by positivity)
        exact (by field_simp : σ*‖z‖ = κ*((σ/κ)*‖z‖)).le.trans hm
      linarith
    · exact (hρκ.trans hk).trans (by nlinarith only [hkp, hq])
  have hlog (i : Fin (n+1)) :
      clippedLog k ρ (matrixOrderedEigenvalues (affineMatrix C W z) i) ≤
        Real.log k + 1/4+(σ/κ)*‖z‖ := by
    have hh := Real.log_le_log (hρ.trans_le (le_max_right _ _)) (hfactor i)
    rw [Real.log_mul hkp.ne' (by positivity : (1+(1/4+(σ/κ)*‖z‖)) ≠ 0)] at hh
    have hsmall := Real.log_le_sub_one_of_pos (show 0 < 1+(1/4+(σ/κ)*‖z‖) by positivity)
    unfold clippedLog
    linarith only [hh, hsmall]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlog i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc
    _ ≤ (n+1:ℝ)*(Real.log k+1/4+(σ/κ)*‖z‖) := by
      simpa only [clippedTrace, Nat.cast_add, Nat.cast_one] using hsum
    _ = _ := by ring

lemma exp_clippedTrace_upper_norm (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {κ σ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ) (hρκ : ρ ≤ κ)
    (hW : ‖W‖ ≤ σ) (hmean : ‖gaussianMatrixCLM C‖ ≤ κ/4)
    {k : ℝ} (hk : κ ≤ k) (z : EuclideanSpace ℝ ι) :
    Real.exp (clippedTrace C W k ρ z) ≤
      k^(n+1)*Real.exp ((n+1:ℝ)/4+((n+1:ℝ)*σ/κ)*‖z‖) := by
  have hh := Real.exp_le_exp.mpr (clippedTrace_upper_norm C W hC hSym hκ hσ hρ hρκ hW hmean hk z)
  have he : Real.exp ((n+1:ℝ)*Real.log k) = k^(n+1) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (hκ.trans_le hk), ← Nat.cast_add_one,
      Real.rpow_natCast]
  have hsum : (n+1:ℝ)*Real.log k+(n+1:ℝ)/4+((n+1:ℝ)*σ/κ)*‖z‖ =
      (n+1:ℝ)*Real.log k+((n+1:ℝ)/4+((n+1:ℝ)*σ/κ)*‖z‖) := by ring
  rw [hsum, Real.exp_add, he] at hh
  exact hh

lemma exp_clippedTrace_integrable (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    (k : ℝ) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hW : ‖W‖ ≤ σ) :
    Integrable (fun z => Real.exp (clippedTrace C W k ρ z)) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hsg := clippedTrace_centered_subGaussian C W hC hSym k hσ hρ hW
  apply ((hsg.integrable_exp_mul 1).mul_const
    (Real.exp (∫ z, clippedTrace C W k ρ z ∂SYK.standardGaussianMeasureOnEuclidean ι))).congr
  apply ae_of_all
  intro z
  simp only [one_mul]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The actual fixed-source Gaussian ball probability used for absorption. -/
def gaussianBallMass (ι : Type*) [Fintype ι] (κ σ : ℝ) : ℝ :=
  (SYK.standardGaussianMeasureOnEuclidean ι).real
    (closedBall (0 : EuclideanSpace ℝ ι) (κ/(4*σ)))

lemma gaussianBallMass_pos {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    0 < gaussianBallMass ι κ σ := gaussian_closedBall_real_pos (by positivity)

lemma absoluteDet_integrable_lower_mean (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hW : ‖W‖ ≤ σ)
    (hmean : ‖gaussianMatrixCLM C‖ ≤ κ/4) {k : ℝ} (hk : κ ≤ k) :
    Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean ι) ∧
    (k/2)^(n+1)*gaussianBallMass ι κ σ ≤
      ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι ∧
    0 < ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let γ := SYK.standardGaussianMeasureOnEuclidean ι
  let B := closedBall (0 : EuclideanSpace ℝ ι) (κ/(4*σ))
  have hi : Integrable (absoluteDet C W k) γ :=
    (exp_clippedTrace_integrable C W hC hSym k hσ hκ hW).mono'
      (absoluteDet_measurable C W k).aestronglyMeasurable (ae_of_all _ (fun z => by
        rw [Real.norm_of_nonneg (absoluteDet_nonneg C W k z)]
        exact absoluteDet_le_exp_clippedTrace C W hC hSym k hκ z))
  have hl : (∫ z in B, (k/2)^(n+1) ∂γ) ≤ ∫ z in B, absoluteDet C W k z ∂γ := by
    apply integral_mono_ae (integrable_const _) hi.restrict
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with z hz
    exact absoluteDet_lower_on_ball C W hC hSym hκ hσ hW hmean hk z hz
  rw [setIntegral_const, smul_eq_mul] at hl
  have hbound : (k/2)^(n+1)*gaussianBallMass ι κ σ ≤ ∫ z, absoluteDet C W k z ∂γ := by
    simpa only [gaussianBallMass, B, γ, mul_comm] using hl.trans
      (setIntegral_le_integral hi (ae_of_all _ (absoluteDet_nonneg C W k)))
  exact ⟨hi, hbound, (mul_pos (pow_pos (half_pos (hκ.trans_le hk)) _)
    (gaussianBallMass_pos hκ hσ)).trans_le hbound⟩

lemma norm_centered_subGaussian :
    HasSubgaussianMGF (fun z : EuclideanSpace ℝ ι => ‖z‖ -
      ∫ w, ‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) 1
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have h := SYK.product_standardGaussian_hasSubgaussianMGF
    (norm : EuclideanSpace ℝ ι → ℝ) 1 (by norm_num)
    (by simpa using (lipschitzWith_one_norm : LipschitzWith 1 (norm : EuclideanSpace ℝ ι → ℝ)))
  simpa using h

/-- An actual uniform normalized exponential bound before raising to powers. -/
lemma clipped_over_raw_upper_norm (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {κ σ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ) (hρκ : ρ ≤ κ)
    (hW : ‖W‖ ≤ σ) (hmean : ‖gaussianMatrixCLM C‖ ≤ κ/4)
    {k : ℝ} (hk : κ ≤ k) (z : EuclideanSpace ℝ ι) :
    Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    ((2:ℝ)^(n+1)/gaussianBallMass ι κ σ)*
      Real.exp ((n+1:ℝ)/4+((n+1:ℝ)*σ/κ)*‖z‖) := by
  have hbase := absoluteDet_integrable_lower_mean C W hC hSym hκ hσ hW hmean hk
  have hp := gaussianBallMass_pos (ι := ι) hκ hσ
  have hkp := hκ.trans_le hk
  apply (div_le_iff₀ hbase.2.2).mpr
  calc
    _ ≤ k^(n+1)*Real.exp ((n+1:ℝ)/4+((n+1:ℝ)*σ/κ)*‖z‖) :=
      exp_clippedTrace_upper_norm C W hC hSym hκ hσ hρ hρκ hW hmean hk z
    _ = (((2:ℝ)^(n+1)/gaussianBallMass ι κ σ)*
        Real.exp ((n+1:ℝ)/4+((n+1:ℝ)*σ/κ)*‖z‖))*
        ((k/2)^(n+1)*gaussianBallMass ι κ σ) := by
      rw [div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase.2.1 (by positivity)

/-- The coefficient of the Gaussian norm in the true fixed-dimension bound. -/
def fixedNormLip (n : ℕ) (κ σ : ℝ) : ℝ := (n+1:ℝ)*σ/κ

/-- Explicit finite-dimension normalization constant, from actual Gaussian
ball probability and the proved true Gaussian norm mean bound. -/
def fixedMomentPrefactor (ι : Type*) [Fintype ι] (n : ℕ) (κ σ : ℝ) : ℝ :=
  ((2:ℝ)^(n+1)/gaussianBallMass ι κ σ)*
    Real.exp ((n+1:ℝ)/4+fixedNormLip n κ σ*Real.sqrt (Fintype.card ι:ℝ))

lemma fixedMomentPrefactor_pos {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    0 < fixedMomentPrefactor ι n κ σ := by
  unfold fixedMomentPrefactor
  exact mul_pos (div_pos (by positivity) (gaussianBallMass_pos hκ hσ)) (Real.exp_pos _)

/-- All actual normalized clipped moments, proved uniformly over the matrix
coefficients and the unbounded spectral shift in the fixed dimensions. -/
theorem fixedDimension_clipped_moment_bound
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hC : ∀ i j, C i j = C j i) (hSym : ∀ z i j, W z i j = W z j i)
    {κ σ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ) (hρκ : ρ ≤ κ)
    (hW : ‖W‖ ≤ σ) (hmean : ‖gaussianMatrixCLM C‖ ≤ κ/4)
    {k : ℝ} (hk : κ ≤ k) (r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun z => (Real.exp (clippedTrace C W k ρ z)/
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
      (SYK.standardGaussianMeasureOnEuclidean ι) ∧
    (∫ z, (Real.exp (clippedTrace C W k ρ z)/
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      (fixedMomentPrefactor ι n κ σ)^r*Real.exp ((fixedNormLip n κ σ)^2/2*r^2) := by
  let γ := SYK.standardGaussianMeasureOnEuclidean ι
  let L := fixedNormLip n κ σ
  let A := fixedMomentPrefactor ι n κ σ
  let m := ∫ z : EuclideanSpace ℝ ι, ‖z‖ ∂γ
  let F : EuclideanSpace ℝ ι → ℝ := fun z =>
    (Real.exp (clippedTrace C W k ρ z)/(∫ w, absoluteDet C W k w ∂γ))^r
  have hL : 0 ≤ L := by dsimp [L, fixedNormLip]; positivity
  have hA : 0 < A := fixedMomentPrefactor_pos hκ hσ
  have hp := gaussianBallMass_pos (ι := ι) hκ hσ
  have hbase := absoluteDet_integrable_lower_mean C W hC hSym hκ hσ hW hmean hk
  have hmeanNorm : m ≤ Real.sqrt (Fintype.card ι:ℝ) :=
    GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card ι
  have hG := norm_centered_subGaussian (ι := ι)
  have hpoint (z : EuclideanSpace ℝ ι) : F z ≤ A^r*Real.exp ((r*L)*(‖z‖-m)) := by
    have hb := Real.rpow_le_rpow
      (div_nonneg (Real.exp_pos _).le hbase.2.2.le)
      (clipped_over_raw_upper_norm C W hC hSym hκ hσ hρ hρκ hW hmean hk z) hr
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul] at hb
    refine hb.trans ?_
    change _ ≤ (fixedMomentPrefactor ι n κ σ)^r*Real.exp ((r*L)*(‖z‖-m))
    unfold fixedMomentPrefactor
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by positivity) _)
    have hm := mul_le_mul_of_nonneg_left hmeanNorm (mul_nonneg hr hL)
    dsimp only [L, fixedNormLip] at hm ⊢
    nlinarith only [hm]
  have hiBound : Integrable (fun z : EuclideanSpace ℝ ι => A^r*Real.exp ((r*L)*(‖z‖-m))) γ :=
    (hG.integrable_exp_mul (r*L)).const_mul _
  have hi : Integrable F γ := by
    apply hiBound.mono'
    · exact (((clippedTrace_lipschitz C W hC hSym k hσ hρ hW).continuous.measurable.exp.div_const _).pow_const r).aestronglyMeasurable
    · apply ae_of_all
      intro z
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (Real.exp_pos _).le hbase.2.2.le) r)]
      exact hpoint z
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z, A^r*Real.exp ((r*L)*(‖z‖-m)) ∂γ := integral_mono hi hiBound hpoint
    _ = A^r*∫ z, Real.exp ((r*L)*(‖z‖-m)) ∂γ := integral_const_mul _ _
    _ ≤ A^r*Real.exp ((r*L)^2/2) :=
      mul_le_mul_of_nonneg_left (by simpa only [mgf, NNReal.coe_one, one_mul, γ, m] using hG.mgf_le (r*L)) (Real.rpow_nonneg hA.le _)
    _ = _ := by congr 2; ring

/-- Uniform raw and clipped determinant moments for fixed matrix and reduced
Gaussian coefficient dimensions, without a rare-event smallness hypothesis.
The constant is chosen before C, W, the positive clipping width and k. -/
theorem fixedDimension_normalized_moments (n : ℕ) {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (C : GOEAsymptotics.GaussianMatrix (n+1))
        (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)),
      (∀ i j, C i j = C j i) → (∀ z i j, W z i j = W z j i) →
      ‖W‖ ≤ σ → ‖gaussianMatrixCLM C‖ ≤ κ/4 →
      ∀ (k ρ : ℝ), κ ≤ k → 0 < ρ → ρ ≤ κ →
      Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean ι) ∧
      0 < ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι ∧
      ∀ r : ℝ, 0 ≤ r →
        Integrable (fun z => (absoluteDet C W k z /
          (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
          (SYK.standardGaussianMeasureOnEuclidean ι) ∧
        Integrable (fun z => (Real.exp (clippedTrace C W k ρ z) /
          (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
          (SYK.standardGaussianMeasureOnEuclidean ι) ∧
        (∫ z, (absoluteDet C W k z /
          (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
          ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
        (∫ z, (Real.exp (clippedTrace C W k ρ z) /
          (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
          ∂SYK.standardGaussianMeasureOnEuclidean ι) ∧
        (∫ z, (Real.exp (clippedTrace C W k ρ z) /
          (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
          ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ K^r*Real.exp (K*r^2) := by
  let A := fixedMomentPrefactor ι n κ σ
  let B := (fixedNormLip n κ σ)^2/2
  let K := max 1 (max A B)
  have h1K : 1 ≤ K := le_max_left _ _
  have hAK : A ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hBK : B ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hA : 0 < A := fixedMomentPrefactor_pos hκ hσ
  refine ⟨K, h1K, ?_⟩
  intro C W hC hSym hW hmean k ρ hk hρ hρκ
  have hbase := absoluteDet_integrable_lower_mean C W hC hSym hκ hσ hW hmean hk
  refine ⟨hbase.1, hbase.2.2, ?_⟩
  intro r hr
  have hclip := fixedDimension_clipped_moment_bound C W hC hSym hκ hσ hρ hρκ hW hmean hk r hr
  have hp (z : EuclideanSpace ℝ ι) :
      (absoluteDet C W k z /(∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r ≤
      (Real.exp (clippedTrace C W k ρ z)/(∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r := by
    apply Real.rpow_le_rpow (div_nonneg (absoluteDet_nonneg C W k z) hbase.2.2.le) _ hr
    exact div_le_div_of_nonneg_right (absoluteDet_le_exp_clippedTrace C W hC hSym k hρ z) hbase.2.2.le
  have hi : Integrable (fun z => (absoluteDet C W k z /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    apply hclip.1.mono'
    · exact ((absoluteDet_measurable C W k).div_const _ |>.pow_const r).aestronglyMeasurable
    · apply ae_of_all
      intro z
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (absoluteDet_nonneg C W k z) hbase.2.2.le) r)]
      exact hp z
  refine ⟨hi, hclip.1, integral_mono hi hclip.1 hp, ?_⟩
  exact hclip.2.trans (mul_le_mul (Real.rpow_le_rpow hA.le hAK hr)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBK (sq_nonneg r)))
    (Real.exp_pos _).le (Real.rpow_nonneg (hA.le.trans hAK) _))

end
end SlowEquilibration.GaussianAffineDeterminant
