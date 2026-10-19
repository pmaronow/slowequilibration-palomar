-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNormMean
public import SlowEquilibration.GaussianMatrixFeatures
public import SlowEquilibration.GaussianCompactFeatureComparison
public import Lemmas.SpinGlass.gaussian_concentration

/-! Expected spectral edge and Gaussian concentration for actual linear
Gaussian symmetric matrices under Frobenius covariance domination. -/

@[expose] public section
namespace SlowEquilibration.GaussianDominatedEdge
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianMatrixFeatures GaussianCompactMaximum
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev UnitSphere (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)

instance unitSphere_nonempty (n : ℕ) : Nonempty (UnitSphere n) := by
  refine ⟨⟨EuclideanSpace.basisFun (Fin (n+1)) ℝ 0, ?_⟩⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0

instance unitSphere_compact (n : ℕ) : CompactSpace (UnitSphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)

lemma unitSphere_norm {n : ℕ} (u : UnitSphere n) : ‖(u : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

lemma rankOne_unit_norm {n : ℕ} (u : UnitSphere n) : ‖rankOneMatrix u.val‖ = 1 := by
  have h := rankOneMatrix_norm_sq u.val
  rw [unitSphere_norm] at h
  nlinarith [norm_nonneg (rankOneMatrix u.val)]

lemma matrix_eigenvalue_norm_le {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    |matrixOrderedEigenvalues A i| ≤ ‖A‖ := by
  rw [matrixOrderedEigenvalues_eq A hA]
  let h := gaussianMatrixCLM_symmetric A hA
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := h.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := h.eigenvectorBasis hn |>.norm_eq_one i
  have he : gaussianMatrixCLM A v = h.eigenvalues hn i • v := h.apply_eigenvectorBasis hn i
  have hh := (gaussianMatrixCLM A).le_opNorm v
  rw [he, norm_smul, Real.norm_eq_abs, hv, mul_one, mul_one] at hh
  exact hh.trans (GOEEdgeConcentration.gaussianMatrixCLM_norm_le A)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def upperEigenvalue (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (g : EuclideanSpace ℝ ι) : ℝ := matrixOrderedEigenvalues (W g) 0

lemma upperEigenvalue_lipschitz (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hW : ∀ g i j, W g i j = W g j i) : LipschitzWith ‖W‖₊ (upperEigenvalue W) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  change |matrixOrderedEigenvalues (W g) 0 - matrixOrderedEigenvalues (W h) 0| ≤ ‖W‖ * ‖g-h‖
  calc
    _ ≤ ‖W g - W h‖ := GOEEdgeConcentration.symmetric_gaussian_eigenvalue_lipschitz _ _ (hW g) (hW h) 0
    _ ≤ _ := by rw [← map_sub]; exact W.le_opNorm _

lemma upperEigenvalue_integrable (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hW : ∀ g i j, W g i j = W g j i) :
    Integrable (upperEigenvalue W) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul ‖W‖).mono'
    (upperEigenvalue_lipschitz W hW).continuous.aestronglyMeasurable
  exact .of_forall fun g => (matrix_eigenvalue_norm_le (W g) (hW g) 0).trans (W.le_opNorm g)

lemma sphereFeature_continuous (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) :
    Continuous (fun u : UnitSphere n => quadraticFeature W u.val) :=
  W.adjoint.continuous.comp (rankOneMatrix_continuous.comp continuous_subtype_val)

lemma sphereFeature_bound (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (u : UnitSphere n) : ‖innerSL ℝ (quadraticFeature W u.val)‖ ≤ ‖W‖ := by
  rw [innerSL_apply_norm]
  change ‖W.adjoint (rankOneMatrix u.val)‖ ≤ ‖W‖
  simpa only [rankOne_unit_norm, mul_one, LinearIsometryEquiv.norm_map] using W.adjoint.le_opNorm (rankOneMatrix u.val)

lemma upperEigenvalue_le_supremum (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hW : ∀ g i j, W g i j = W g j i) (g : EuclideanSpace ℝ ι) :
    upperEigenvalue W g ≤ ⨆ u : UnitSphere n, inner ℝ (quadraticFeature W u.val) g := by
  let h := gaussianMatrixCLM_symmetric (W g) (hW g)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := h.eigenvectorBasis hn 0
  have hv : ‖v‖ = 1 := h.eigenvectorBasis hn |>.norm_eq_one 0
  let u : UnitSphere n := ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
  have he : inner ℝ (quadraticFeature W u.val) g = upperEigenvalue W g := by
    rw [quadraticFeature_apply, upperEigenvalue, matrixOrderedEigenvalues_eq (W g) (hW g)]
    change inner ℝ v (gaussianMatrixCLM (W g) v) = h.eigenvalues hn 0
    have hev : gaussianMatrixCLM (W g) v = h.eigenvalues hn 0 • v := h.apply_eigenvectorBasis hn 0
    rw [hev, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    simp
  rw [← he]
  exact le_field_supremum (fun u : UnitSphere n => innerSL ℝ (quadraticFeature W u.val))
    (sphereFeature_bound W) g u


lemma featureSupremum_integrable {V : Type*} [Nonempty V] [TopologicalSpace V] [CompactSpace V]
    (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Integrable (fun g => ⨆ v, inner ℝ (a v) g) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  let L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ := fun v => innerSL ℝ (a v)
  have hL : Continuous L := (innerSL ℝ).continuous.comp ha
  obtain ⟨K, hK, hb⟩ := exists_feature_bound L hL
  apply (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K).mono'
    (field_supremum_lipschitz L hb).continuous.aestronglyMeasurable
  exact .of_forall fun g => norm_field_supremum_le L hb g

/-- The spectral edge mean is proved by actual compact Gaussian comparison,
not supplied as a spectral or probabilistic premise. -/
theorem mean_upperEigenvalue_le (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ g i j, W g i j = W g j i)
    {σ : ℝ} (hσ : 0 ≤ σ) (hW : ‖W‖ ≤ σ) :
    (∫ g, upperEigenvalue W g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      (Real.sqrt 2 * σ) * Real.sqrt (n+1 : ℝ) := by
  let a : UnitSphere n → EuclideanSpace ℝ ι := fun u => quadraticFeature W u.val
  let b : UnitSphere n → EuclideanSpace ℝ (Fin (n+1)) := fun u => (Real.sqrt 2 * σ) • u.val
  have ha : Continuous a := sphereFeature_continuous W
  have hb : Continuous b := by
    dsimp only [b]
    fun_prop
  have hc : 0 ≤ Real.sqrt 2 * σ := mul_nonneg (Real.sqrt_nonneg _) hσ
  have hinc (u v : UnitSphere n) : ‖a u-a v‖ ≤ ‖b u-b v‖ := by
    dsimp only [a, b]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact quadraticFeature_unit_increment W hσ hW u.val v.val (unitSphere_norm u) (unitSphere_norm v)
  have hcomp := GaussianCompactFeatureComparison.expected_supremum_comparison_of_increment_norm a b ha hb hinc
  have hlo := integral_mono (upperEigenvalue_integrable W hSym)
    (featureSupremum_integrable a ha) (upperEigenvalue_le_supremum W hSym)
  have hup := integral_mono (featureSupremum_integrable b hb)
    (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul (Real.sqrt 2 * σ)) (fun g => by
      apply ciSup_le
      intro u
      have h := real_inner_le_norm (b u) g
      simpa only [b, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, unitSphere_norm, mul_one] using h)
  rw [integral_const_mul] at hup
  have hnorm := GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card (Fin (n+1))
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hnorm
  exact (hlo.trans hcomp |>.trans hup).trans (mul_le_mul_of_nonneg_left hnorm hc)

/-- Sharp centered Gaussian concentration for the actual top eigenvalue of
any such linear symmetric matrix, with its true covariance upper bound. -/
theorem upperEigenvalue_centered_subGaussian
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ g i j, W g i j = W g j i)
    {σ : ℝ} (hσ : 0 < σ) (hW : ‖W‖ ≤ σ) :
    HasSubgaussianMGF (fun g => upperEigenvalue W g -
      ∫ h, upperEigenvalue W h ∂SYK.standardGaussianMeasureOnEuclidean ι)
      (σ^2).toNNReal (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply SYK.product_standardGaussian_hasSubgaussianMGF (upperEigenvalue W) σ hσ
  exact (upperEigenvalue_lipschitz W hSym).weaken (by
    change ‖W‖ ≤ (σ.toNNReal : ℝ)
    rw [Real.coe_toNNReal _ hσ.le]
    exact hW)

/-- Actual finite-dimensional outside-edge probability, uniform in the
matrix dimension and the number of original Gaussian coefficients. -/
theorem upperEigenvalue_tail
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ g i j, W g i j = W g j i)
    {σ : ℝ} (hσ : 0 < σ) (hW : ‖W‖ ≤ σ) {t : ℝ} (ht : 0 ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g | (Real.sqrt 2 * σ) * Real.sqrt (n+1 : ℝ) + t ≤ upperEigenvalue W g} ≤
      Real.exp (-t^2/(2*σ^2)) := by
  have hmean := mean_upperEigenvalue_le W hSym hσ.le hW
  have htail := (upperEigenvalue_centered_subGaussian W hSym hσ hW).measure_ge_le ht
  rw [Real.coe_toNNReal _ (sq_nonneg σ)] at htail
  refine (measureReal_mono (fun g hg => ?_)).trans htail
  change (Real.sqrt 2 * σ) * Real.sqrt (n+1 : ℝ) + t ≤ upperEigenvalue W g at hg
  change t ≤ upperEigenvalue W g - _
  linarith


lemma eigenvalue_add_perturbation_le (A C : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i) (i : Fin (n+1)) :
    matrixOrderedEigenvalues (C+A) i ≤ matrixOrderedEigenvalues A i + ‖gaussianMatrixCLM C‖ := by
  have hCA : ∀ i j, (C+A) i j = (C+A) j i := fun i j => by
    change C i j + A i j = C j i + A j i
    rw [hC i j, hA i j]
  rw [matrixOrderedEigenvalues_eq _ hCA, matrixOrderedEigenvalues_eq _ hA]
  have hh := symmetric_eigenvalue_norm_bound (gaussianMatrixCLM (C+A)) (gaussianMatrixCLM A)
    (gaussianMatrixCLM_symmetric _ hCA) (gaussianMatrixCLM_symmetric _ hA)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) i
  have he : gaussianMatrixCLM (C+A)-gaussianMatrixCLM A = gaussianMatrixCLM C := by
    rw [show gaussianMatrixCLM (C+A) = gaussianMatrixCLM C+gaussianMatrixCLM A from
      (gaussianMatrixToCLM (n+1)).map_add C A]
    exact add_sub_cancel_right _ _
  rw [he] at hh
  linarith [(abs_le.mp hh).2]

lemma eigenvalue_le_upper (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    matrixOrderedEigenvalues A i ≤ matrixOrderedEigenvalues A 0 := by
  rw [matrixOrderedEigenvalues_eq A hA]
  exact (gaussianMatrixCLM_symmetric A hA).eigenvalues_antitone _ (Fin.zero_le i)

lemma covariance_edge_scale_le {N : ℕ} (hN : n+1 ≤ N) {b : ℝ} (hb : 0 ≤ b) :
    (Real.sqrt 2 * Real.sqrt (2*b/N)) * Real.sqrt (n+1 : ℝ) ≤ 2 * Real.sqrt b := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hnN : (n+1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbn : 0 ≤ 2*b/(N : ℝ) := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hbn, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n+1),
    mul_pow, Real.sq_sqrt hb]
  have h := (div_le_iff₀ hNp).mpr (mul_le_mul_of_nonneg_left hnN (mul_nonneg (by norm_num : (0:ℝ)≤4) hb))
  convert h using 1 <;> ring

/-- The exact manuscript variance scale gives a dimension-uniform edge
bound, without a limiting spectral-law assumption. -/
theorem upperEigenvalue_tail_covarianceScale
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ g i j, W g i j = W g j i)
    {N : ℕ} (hN : n+1 ≤ N) {b : ℝ} (hb : 0 < b)
    (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) {t : ℝ} (ht : 0 ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g | 2 * Real.sqrt b + t ≤ upperEigenvalue W g} ≤
      Real.exp (-(N : ℝ)*t^2/(4*b)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hσ : 0 < Real.sqrt (2*b/N) := Real.sqrt_pos.mpr (by positivity)
  have htail := upperEigenvalue_tail W hSym hσ hW ht
  have hscale := covariance_edge_scale_le hN hb.le
  have he : -t^2/(2*(Real.sqrt (2*b/N))^2) = -(N : ℝ)*t^2/(4*b) := by
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*b/N)]
    field_simp
    <;> ring
  rw [he] at htail
  refine (measureReal_mono (fun g hg => ?_)).trans htail
  change (Real.sqrt 2 * Real.sqrt (2*b/N)) * Real.sqrt (n+1 : ℝ) + t ≤ upperEigenvalue W g
  change 2 * Real.sqrt b + t ≤ upperEigenvalue W g at hg
  linarith

/-- A deterministic mean bounded in operator norm preserves the fixed gap
outside an exponentially small, explicitly measured Gaussian event. -/
theorem affine_fixed_gap_probability
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j, W z i j = W z j i)
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (hC : ∀ i j, C i j = C j i)
    {N : ℕ} (hN : n+1 ≤ N) {b g : ℝ} (hb : 0 < b) (hg : 0 < g)
    (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) (hmean : ‖gaussianMatrixCLM C‖ ≤ g/4) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {z | ∃ i, 2*Real.sqrt b+g/2 < matrixOrderedEigenvalues (C+W z) i} ≤
      Real.exp (-(N : ℝ)*g^2/(64*b)) := by
  have ht := upperEigenvalue_tail_covarianceScale W hSym hN hb hW
    (show 0 ≤ g/4 by positivity)
  have he : -(N : ℝ)*(g/4)^2/(4*b) = -(N : ℝ)*g^2/(64*b) := by ring
  rw [he] at ht
  refine (measureReal_mono (fun z hz => ?_)).trans ht
  obtain ⟨i, hi⟩ := hz
  have hpert := eigenvalue_add_perturbation_le (W z) C (hSym z) hC i
  have htop := eigenvalue_le_upper (W z) (hSym z) i
  change 2*Real.sqrt b+g/4 ≤ upperEigenvalue W z
  unfold upperEigenvalue
  linarith

end
end SlowEquilibration.GaussianDominatedEdge
