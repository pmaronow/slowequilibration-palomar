-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureOnePointSignedSlope
public import SlowEquilibration.GOEPureSignedMaximumTransfer
public import SlowEquilibration.GOEClippedAdjugateTransfer
public import SlowEquilibration.GOEPhysicalClippedDeterminantMoments
public import SlowEquilibration.GOEMaximumAllDimensionPositivity
public import SlowEquilibration.SignedExponentialNormalizedMoments
public import SlowEquilibration.WeightedTraceMean
public import SlowEquilibration.SphericalCountIntensityRates
public import SlowEquilibration.SourcePureLocalMaxFullCenterLimits
public import SlowEquilibration.SourcePureCriticalCenterCountLimits
public import SlowEquilibration.SourcePureCriticalTailCountLimit
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The moving spectral cutoff in manuscript `prop:mo-pure`.
The local-maximum determinant is differentiated as an ordinary expectation,
including its moving boundary. The excluded adjugate estimate and the finite
Hermite resolvent estimate give the actual physical intensity's uniform
inverse-dimension logarithmic slope error. Scalar companion results identify
the singular joint count measures, normalize the maximum Palm kernel,
identify radial and energy truncations exactly, and assemble the contact
quadratic bound and common-center first-moment limits. These companion
results do not assert the full localization/filter package of part (d).

The only additional literature interface is
absence of atoms for the largest GOE eigenvalue, a consequence of Anderson,
Guionnet and Zeitouni, *An Introduction to Random Matrices*, Theorem 2.5.2
(joint eigenvalue density). It is a proposition supplied explicitly, rather
than an axiom or an assumption about determinant derivatives. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureDeterminantDerivative
open MeasureTheory ProbabilityTheory Set Filter Polynomial
open GOEAsymptotics GOERawMoments GOEMaximumDeterminant GOEPhysicalPotential
open GOEPhysicalClippedDeterminantMoments GOEScaling GOEClippedDeterminants
open GOEAdjugateJacobiMean GOEPhysicalSignedMean GOEPurePhysicalSignedSlope
open GOEPureSignedMaximumTransfer SphericalMarkedWindows
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open scoped Topology ENNReal NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-- The no-atom consequence of AGZ, Theorem 2.5.2, in the repository's
physical variance convention. Off-diagonal variance is `b/N` and diagonal
variance is `2*b/N`. Only a positive variance and ambient dimension are used.
Reference: https://www.wisdom.weizmann.ac.il/~zeitouni/cupbook.pdf . -/
def GOENoFixedTopEigenvalue : Prop :=
  ∀ (n N : ℕ), 0 < N → ∀ b : ℝ, 0 < b → ∀ k : ℝ,
    ∀ᵐ W ∂SphericalGaussianJet.goeLaw (n+1) N b, eigenvalues n W 0 ≠ k

private def spectralPolynomial (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ[X] :=
  ∏ i, (X-C (eigenvalues n W i))

private lemma spectralPolynomial_eval (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : ℝ) :
    (spectralPolynomial n W).eval k = ∏ i, (k-eigenvalues n W i) := by
  simp [spectralPolynomial, eval_prod]

private lemma spectralPolynomial_root (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (spectralPolynomial n W).eval (eigenvalues n W 0)=0 := by
  rw [spectralPolynomial_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ 0) (sub_self _)

private lemma spectralPolynomial_derivative (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : ℝ) :
    (spectralPolynomial n W).derivative.eval k =
      ∑ i : Fin (n+1), ∏ j ∈ Finset.univ.erase i, (k-eigenvalues n W j) := by
  simp [spectralPolynomial, derivative_prod_finset, eval_finsetSum, eval_prod]

private lemma spectralPolynomial_eq_det (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hW : ∀ i j, W i j=W j i) (k : ℝ) :
    (spectralPolynomial n W).eval k=(k • 1-W).det := by
  rw [spectralPolynomial_eval]
  simpa only [eigenvalues, gaussianToMatrix_matrixToGaussian] using
    (shifted_det_eq_prod k (matrixToGaussian W) hW).symm

private lemma spectralPolynomial_eq_adjugate (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hW : ∀ i j, W i j=W j i) (k : ℝ) :
    (spectralPolynomial n W).derivative.eval k=(k • 1-W).adjugate.trace := by
  have hH : W.IsHermitian := by ext i j; exact hW j i
  rw [shifted_adjugate_trace_eq_derivative W hH]
  have hP : spectralPolynomial n W=W.charpoly := by
    simpa only [spectralPolynomial, eigenvalues, gaussianToMatrix_matrixToGaussian] using
      (symmetric_gaussian_charpoly (matrixToGaussian W) hW).symm
  rw [hP]

/-- The ordinary adjugate mean on negative Hessians; no inverse is used,
so the integrand also makes sense at singular matrices. -/
def maximumAdjugateMean (n N : ℕ) (b k : ℝ) : ℝ :=
  ∫ W in maximumEvent n k, (k • 1-W).adjugate.trace
    ∂SphericalGaussianJet.goeLaw (n+1) N b

private lemma clippedDet_integrable (n N : ℕ) (hN : 0 < N)
    {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (k : ℝ) :
    Integrable (matrixClippedDet n k ρ) (SphericalGaussianJet.goeLaw (n+1) N b) := by
  let a := scaleFactor n N b
  have ha : 0 < a := scaleFactor_pos n hN hb
  have hmap : Measurable (fun A : GaussianMatrix (n+1) =>
      a • GOEDeterminantMoments.realization n A) := by
    exact (measurable_const (a := a)).smul (GOEDeterminantMoments.realization_measurable n)
  rw [← scaled_realization_law n hN hb.le]
  apply (integrable_map_measure (matrixClippedDet_measurable n k ρ).aestronglyMeasurable
    hmap.aemeasurable).mpr
  have hi := SignedExponentialNormalizedMoments.exponential_integrable
    (clippedTrace_centered_subGaussian n (k/a) (div_pos hρ ha))
  convert hi.const_mul (a^(n+1)) using 1
  funext A
  change matrixClippedDet n k ρ (a • GOEDeterminantMoments.realization n A)=_
  rw [show ρ=a*(ρ/a) by field_simp,
    matrixClippedDet_scale n ha (div_pos hρ ha), matrixClippedDet_realization]
  congr 2
  field_simp

private lemma clippedDet_eq_prod (n : ℕ) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    matrixClippedDet n k ρ W=∏ i, max |k-eigenvalues n W i| ρ := by
  unfold matrixClippedDet
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (hρ.trans_le (le_max_right _ _))

private lemma spectralPolynomial_derivative_bound (n : ℕ) (k t : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (ht : |t-k| ≤ ρ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    |(spectralPolynomial n W).derivative.eval t| ≤
      (n+1 : ℝ)*2^n/ρ*matrixClippedDet n k ρ W := by
  rw [spectralPolynomial_derivative]
  have hterm (j : Fin (n+1)) : |t-eigenvalues n W j| ≤
      2*max |k-eigenvalues n W j| ρ := by
    have h := abs_add_le (t-k) (k-eigenvalues n W j)
    rw [sub_add_sub_cancel] at h
    have h1 := le_max_left |k-eigenvalues n W j| ρ
    have h2 := le_max_right |k-eigenvalues n W j| ρ
    linarith
  have hp (i : Fin (n+1)) :
      |∏ j ∈ Finset.univ.erase i, (t-eigenvalues n W j)| ≤
        2^n/ρ*matrixClippedDet n k ρ W := by
    rw [Finset.abs_prod]
    have hprod := Finset.prod_le_prod₀ (fun j (_ : j ∈ Finset.univ.erase i) => abs_nonneg (t-eigenvalues n W j))
      (fun j (_ : j ∈ Finset.univ.erase i) => hterm j)
    simp only [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] at hprod
    have hnonneg : 0 ≤ ∏ j ∈ Finset.univ.erase i, max |k-eigenvalues n W j| ρ :=
      Finset.prod_nonneg (fun j _ => (abs_nonneg _).trans (le_max_left _ _))
    have hmul := mul_le_mul_of_nonneg_left (le_max_right |k-eigenvalues n W i| ρ) hnonneg
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← clippedDet_eq_prod n k hρ W] at hmul
    have hh := mul_le_mul_of_nonneg_left hmul (show (0:ℝ) ≤ 2^n by positivity)
    have he : 2^n/ρ*matrixClippedDet n k ρ W =
        (2^n*matrixClippedDet n k ρ W)/ρ := by ring
    rw [he]
    apply (le_div_iff₀ hρ).mpr
    exact (mul_le_mul_of_nonneg_right hprod hρ.le).trans (by nlinarith [hh])
  calc
    _ ≤ ∑ i : Fin (n+1), |∏ j ∈ Finset.univ.erase i, (t-eigenvalues n W j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n+1), 2^n/ρ*matrixClippedDet n k ρ W := Finset.sum_le_sum (fun i _ => hp i)
    _ = _ := by simp; ring

private lemma cutoff_polynomial_lipschitz (P : ℝ[X]) (r l u : ℝ)
    (hroot : P.eval r=0) {K : ℝ≥0}
    (hP : LipschitzOnWith K P.eval (Icc l u)) :
    LipschitzOnWith K (fun t => if r<t then P.eval t else 0) (Icc l u) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  by_cases hrl : r<l
  · simpa only [ite_eq_left (hrl.trans_le ht.1),ite_eq_left (hrl.trans_le hs.1)] using hP.dist_le_mul t ht s hs
  by_cases hur : u<r
  · simp only [ite_eq_right (not_lt.mpr (ht.2.trans hur.le)),
      ite_eq_right (not_lt.mpr (hs.2.trans hur.le)),dist_self]
    positivity
  have hr : r ∈ Icc l u := ⟨le_of_not_gt hrl,le_of_not_gt hur⟩
  have hc := hP.comp (LipschitzWith.id.max_const r).lipschitzOnWith
    (fun t (ht : t ∈ Icc l u) =>
      (show max t r ∈ Icc l u from ⟨ht.1.trans (le_max_left _ _),max_le ht.2 hr.2⟩))
  simp only [mul_one] at hc
  have he (x : ℝ) : (if r<x then P.eval x else 0)=P.eval (max x r) := by
    by_cases hx : r<x
    · simp [hx,max_eq_left hx.le]
    · simp [hx,max_eq_right (le_of_not_gt hx),hroot]
  simpa only [he,Function.comp_apply,id_eq] using hc.dist_le_mul t ht s hs

private def cutoffWeight (n : ℕ) (k : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  if eigenvalues n W 0<k then (spectralPolynomial n W).eval k else 0

private def cutoffDerivative (n : ℕ) (k : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  if eigenvalues n W 0<k then (spectralPolynomial n W).derivative.eval k else 0

private lemma cutoffWeight_measurable (n : ℕ) (k : ℝ) : Measurable (cutoffWeight n k) := by
  have hm : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      (spectralPolynomial n W).eval k) := by
    simp only [spectralPolynomial_eval]
    exact Finset.measurable_prod _ (fun i _ =>
      measurable_const.sub ((measurable_pi_apply i).comp (eigenvalues_measurable n)))
  exact Measurable.ite (maximumEvent_measurable n k) hm measurable_const

private lemma cutoffDerivative_measurable (n : ℕ) (k : ℝ) : Measurable (cutoffDerivative n k) := by
  have hm : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      (spectralPolynomial n W).derivative.eval k) := by
    simp only [spectralPolynomial_derivative]
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_prod _ (fun j _ =>
      measurable_const.sub ((measurable_pi_apply j).comp (eigenvalues_measurable n))))
  exact Measurable.ite (maximumEvent_measurable n k) hm measurable_const

private lemma cutoffWeight_eq_indicator (n : ℕ) (k : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hW : ∀ i j, W i j=W j i) :
    cutoffWeight n k W=(maximumEvent n k).indicator (matrixAbsoluteDet n k) W := by
  by_cases ht : W ∈ maximumEvent n k
  · change eigenvalues n W 0<k at ht
    rw [indicator_of_mem (show W ∈ maximumEvent n k from ht)]
    simp only [cutoffWeight,ite_eq_left ht,spectralPolynomial_eq_det n W hW k,matrixAbsoluteDet,
      abs_of_pos (shifted_determinant_pos_of_maximumEvent n W hW ht)]
  · change ¬ eigenvalues n W 0<k at ht
    simp only [cutoffWeight,ite_eq_right ht,indicator_of_notMem (show W ∉ maximumEvent n k from ht)]

private lemma cutoffWeight_hasDerivAt (n : ℕ) (k : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hW : eigenvalues n W 0 ≠ k) :
    HasDerivAt (fun t => cutoffWeight n t W) (cutoffDerivative n k W) k := by
  rcases lt_or_gt_of_ne hW with ht | ht
  · have heq : (fun t => cutoffWeight n t W) =ᶠ[𝓝 k] (spectralPolynomial n W).eval := by
      filter_upwards [Ioi_mem_nhds ht] with t ht
      change eigenvalues n W 0<t at ht
      simp only [cutoffWeight,ite_eq_left ht]
    simpa only [cutoffDerivative,ite_eq_left ht] using
      ((spectralPolynomial n W).hasDerivAt k).congr_of_eventuallyEq heq
  · have heq : (fun t => cutoffWeight n t W) =ᶠ[𝓝 k] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds ht] with t ht
      simp only [cutoffWeight,ite_eq_right (not_lt.mpr ht.le)]
    simpa only [cutoffDerivative,ite_eq_right (not_lt.mpr ht.le)] using
      (hasDerivAt_const k (0 : ℝ)).congr_of_eventuallyEq heq


/-- Differentiation of the actual maximum-restricted determinant expectation.
The moving boundary contributes zero because the determinant vanishes there;
the integrable local Lipschitz majorant justifies differentiation under the
integral. The displayed derivative is the ordinary restricted adjugate mean. -/
theorem maximumMean_hasDerivAt (hGOE : GOENoFixedTopEigenvalue)
    (n N : ℕ) (hN : 0<N) {b : ℝ} (hb : 0<b) (k : ℝ) :
    HasDerivAt (maximumMean n N b) (maximumAdjugateMean n N b k) k := by
  let ν := SphericalGaussianJet.goeLaw (n+1) N b
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ → ℝ :=
    fun W => (n+1 : ℝ)*2^n*matrixClippedDet n k 1 W
  have hB (W) : 0 ≤ B W := mul_nonneg (by positivity) (matrixClippedDet_pos n k 1 W).le
  have hBi : Integrable B ν := (clippedDet_integrable n N hN hb (by norm_num) k).const_mul _
  have hFI : Integrable (cutoffWeight n k) ν := by
    have hD : Integrable (matrixAbsoluteDet n k) ν := by
      have he (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
          matrixAbsoluteDet n k W=|(W-k • 1).det| := by
        unfold matrixAbsoluteDet
        rw [show k • 1-W=-(W-k • 1) by abel,Matrix.det_neg,abs_mul,abs_pow]
        simp
      convert (UnrestrictedConditionedDeterminants.fixed_shifted_determinant_integrable (n+1) N b k).abs using 1
      funext W
      exact he W
    apply (hD.indicator (maximumEvent_measurable n k)).congr
    filter_upwards [goe_symmetric_ae (n+1) N b] with W hW
    exact (cutoffWeight_eq_indicator n k W hW).symm
  have hLip : ∀ W, LipschitzOnWith (Real.nnabs (B W))
      (fun t => cutoffWeight n t W) (Icc (k-1) (k+1)) := by
    intro W
    apply cutoff_polynomial_lipschitz _ _ _ _ (spectralPolynomial_root n W)
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    have hbound : ∀ y ∈ Icc (k-1) (k+1),
        ‖deriv (spectralPolynomial n W).eval y‖ ≤ B W := by
      intro y hy
      rw [(spectralPolynomial n W).hasDerivAt y |>.deriv,Real.norm_eq_abs]
      have hh := spectralPolynomial_derivative_bound n k y (by norm_num : (0:ℝ)<1)
        (abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩) W
      simpa only [div_one,B] using hh
    have hh := (convex_Icc (k-1) (k+1)).norm_image_sub_le_of_norm_deriv_le
      (fun y _ => (spectralPolynomial n W).differentiableAt) hbound hs ht
    simpa only [Real.dist_eq,Real.norm_eq_abs,Real.coe_nnabs,abs_of_nonneg (hB W)] using hh
  obtain ⟨_,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := ν) (bound := B) (F := cutoffWeight n) (F' := cutoffDerivative n k)
    (Icc_mem_nhds (by linarith : k-1<k) (by linarith : k<k+1))
    (.of_forall fun t => (cutoffWeight_measurable n t).aestronglyMeasurable) hFI
    (cutoffDerivative_measurable n k).aestronglyMeasurable
    (.of_forall hLip) hBi
    ((hGOE n N hN b hb k).mono fun W hW => cutoffWeight_hasDerivAt n k W hW)
  have hmean (t : ℝ) : (∫ W, cutoffWeight n t W ∂ν)=maximumMean n N b t := by
    rw [maximumMean,← integral_indicator (maximumEvent_measurable n t)]
    apply integral_congr_ae
    filter_upwards [goe_symmetric_ae (n+1) N b] with W hW
    exact cutoffWeight_eq_indicator n t W hW
  have hderiv : (∫ W, cutoffDerivative n k W ∂ν)=maximumAdjugateMean n N b k := by
    rw [maximumAdjugateMean,← integral_indicator (maximumEvent_measurable n k)]
    apply integral_congr_ae
    filter_upwards [goe_symmetric_ae (n+1) N b] with W hW
    by_cases ht : W ∈ maximumEvent n k
    · change eigenvalues n W 0<k at ht
      simp only [cutoffDerivative,ite_eq_left ht,indicator_of_mem (show W ∈ maximumEvent n k from ht),
        spectralPolynomial_eq_adjugate n W hW k]
    · change ¬ eigenvalues n W 0<k at ht
      simp only [cutoffDerivative,ite_eq_right ht,indicator_of_notMem (show W ∉ maximumEvent n k from ht)]
  simpa only [hmean,hderiv] using hd

private lemma adjugate_abs_le_clipped (n : ℕ) (k : ℝ) {ρ : ℝ} (hρ : 0<ρ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hW : ∀ i j, W i j=W j i) :
    |(k • 1-W).adjugate.trace| ≤ (n+1 : ℝ)/ρ*matrixClippedDet n k ρ W := by
  rw [← spectralPolynomial_eq_adjugate n W hW k,spectralPolynomial_derivative]
  have hp (i : Fin (n+1)) :
      |∏ j ∈ Finset.univ.erase i, (k-eigenvalues n W j)| ≤ matrixClippedDet n k ρ W/ρ := by
    rw [Finset.abs_prod]
    apply (le_div_iff₀ hρ).mpr
    calc
      _ ≤ (∏ j ∈ Finset.univ.erase i, max |k-eigenvalues n W j| ρ)*
          max |k-eigenvalues n W i| ρ :=
        mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => le_max_left _ _))
          (le_max_right _ _) hρ.le (Finset.prod_nonneg (fun _ _ => (abs_nonneg _).trans (le_max_left _ _)))
      _ = matrixClippedDet n k ρ W := by
        rw [clippedDet_eq_prod n k hρ,Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun i _ => hp i)).trans_eq (by simp; ring))

private lemma adjugate_integrable (n N : ℕ) (hN : 0<N) {b : ℝ} (hb : 0<b) (k : ℝ) :
    Integrable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => (k • 1-W).adjugate.trace)
      (SphericalGaussianJet.goeLaw (n+1) N b) := by
  apply ((clippedDet_integrable n N hN hb (by norm_num : (0:ℝ)<1) k).const_mul (n+1 : ℝ)).mono'
    ((continuous_const.sub continuous_id).matrix_adjugate.matrix_trace.aestronglyMeasurable)
  filter_upwards [goe_symmetric_ae (n+1) N b] with W hW
  simpa only [Real.norm_eq_abs,div_one,Pi.sub_apply,id_eq] using adjugate_abs_le_clipped n k (by norm_num : (0:ℝ)<1) W hW

private lemma adjugate_integral_eq_signed_derivative (n N : ℕ) (hN : 0<N)
    {b : ℝ} (hb : 0<b) (k : ℝ) :
    (∫ W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, (k • 1-W).adjugate.trace
      ∂SphericalGaussianJet.goeLaw (n+1) N b)=
        (n+1 : ℝ)*signedPhysicalMean n N b k := by
  have hs : 2*(Real.sqrt (b/(2*N)))^2=b/N := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ b/(2*(N:ℝ)))]; field_simp
  have hmap := goeLaw_bridge (n+1) N b (Real.sqrt (b/(2*N))) hs
  have hi := integral_map (μ := SphericalGaussianJet.goeLaw (n+1) N b)
    (matrixToGaussian_measurable (n+1)).aemeasurable
    (show AEStronglyMeasurable (fun A : GaussianMatrix (n+1) =>
      (GOEExpectedDeterminant.shifted (n+1) k A).adjugate.trace)
        ((SphericalGaussianJet.goeLaw (n+1) N b).map matrixToGaussian) by
      apply Continuous.aestronglyMeasurable
      apply Continuous.matrix_trace
      apply Continuous.matrix_adjugate
      unfold GOEExpectedDeterminant.shifted
      fun_prop)
  rw [hmap,GOEExpectedDeterminant.mean_adjugate_trace] at hi
  rw [signedPhysicalMean_eq_meanDet n hN hb.le k]
  exact hi.symm

private lemma square_moment_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) {K q : ℝ}
    (hi : Integrable (fun w => f w^2) ν) (hK : (∫ w, f w^2 ∂ν) ≤ K)
    (B : Set Ω) (hB : MeasurableSet B) (hq : ν.real B ≤ q) :
    (∫ w in B, f w ∂ν) ≤ Real.sqrt K*Real.sqrt q := by
  have hF : MemLp f 2 ν := (memLp_two_iff_integrable_sq hf).mpr hi
  have hφ : MemLp (B.indicator (fun _ => (1 : ℝ))) 2 ν :=
    memLp_indicator_const _ hB _ (Or.inr (measure_ne_top ν B))
  have hh := WeightedTraceMean.abs_integral_mul_le_sqrt hF hφ
  have he : (∫ w, f w*B.indicator (fun _ => (1 : ℝ)) w ∂ν)=∫ w in B, f w ∂ν := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    exact .of_forall fun w => by by_cases hw : w ∈ B <;> simp [hw]
  have he2 : (∫ w, (B.indicator (fun _ => (1 : ℝ)) w)^2 ∂ν)=ν.real B := by
    have heq : (fun w => (B.indicator (fun _ => (1 : ℝ)) w)^2)=B.indicator (fun _ => (1 : ℝ)) := by
      funext w; by_cases hw : w ∈ B <;> simp [hw]
    rw [heq,integral_indicator hB]
    simp
  rw [he,he2] at hh
  exact (le_abs_self _).trans (hh.trans (mul_le_mul (Real.sqrt_le_sqrt hK)
    (Real.sqrt_le_sqrt hq) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))


/-- The signed adjugate mean and the maximum-restricted adjugate mean differ
by an exponentially small relative error, including the matrix-size factor.
This estimate is proved independently of the no-atom literature interface. -/
theorem excluded_adjugate_relative_loss {b g Z : ℝ} (hb : 0<b) (hg : 0<g) :
    ∃ C c : ℝ, 0<C ∧ 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      |(n+1 : ℝ)*signedPhysicalMean n (n+2) b k-maximumAdjugateMean n (n+2) b k| ≤
        C*(n+2 : ℕ)*Real.exp (-c*(n+2 : ℕ))*maximumMean n (n+2) b k := by
  let ρ := g/(2*Real.sqrt b)
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  let K := (2:ℝ)^2*Real.exp (4*b*2^2/g^2)
  let c := (g/Real.sqrt b)^2/(64*Real.pi^2)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨(4/g)*Real.sqrt K,c,by dsimp [K]; positivity,hc,?_⟩
  obtain ⟨Craw,hCraw,hraw⟩ := GOEPhysicalNormalizedMoments.normalized_physical_moments
    1 (b := b) (g := g) (Z := Z) (r := 2) hb hg (by norm_num)
  filter_upwards [physical_clipped_normalized_moments_eventually hb hg hρ (le_refl ρ),
    nonmaximum_probability_eventually hb hg,
    maximumMean_comparison_eventually (Z := Z) hb hg] with n hMom hprob hcomp
  intro k hk
  let ν := SphericalGaussianJet.goeLaw (n+1) (n+2) b
  let a := scaleFactor n (n+2) b
  let M := physicalMean n (n+2) b k
  have ha : 0<a := scaleFactor_pos n (by omega) hb
  have hM : 0<M := (hraw n k hk.1 hk.2).2.1
  have hI := adjugate_integrable n (n+2) (by omega) hb k
  have hsplit := integral_add_compl (maximumEvent_measurable n k) hI
  rw [adjugate_integral_eq_signed_derivative n (n+2) (by omega) hb k] at hsplit
  have hdiff : (n+1 : ℝ)*signedPhysicalMean n (n+2) b k-maximumAdjugateMean n (n+2) b k=
      ∫ W in (maximumEvent n k)ᶜ, (k • 1-W).adjugate.trace ∂ν := by
    change maximumAdjugateMean n (n+2) b k+_=_ at hsplit
    linarith
  obtain ⟨hmi,hm⟩ := hMom (n+2) (by omega) k hk.1 2 (by norm_num)
  simp only [Real.rpow_two] at hmi hm
  have hTail := square_moment_event_bound ν
    ((matrixClippedDet_measurable n k (a*ρ)).div_const M).aestronglyMeasurable
    hmi hm _ (maximumEvent_measurable n k).compl (hprob k hk.1)
  have hexp : Real.sqrt (Real.exp (-(n+1 : ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2))) ≤
      Real.exp (-c*(n+2 : ℕ)) := by
    rw [Real.sqrt_eq_rpow,← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n+2 : ℕ) ≤ 2*(n+1 : ℝ) := by push_cast; linarith
    have hh := mul_le_mul_of_nonneg_right hn hc.le
    have he : (-(n+1 : ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2))*(1/2)=
        -(2*(n+1 : ℝ)*c) := by dsimp [c]; ring
    rw [he]; linarith
  have hClip : (∫ W in (maximumEvent n k)ᶜ, matrixClippedDet n k (a*ρ) W ∂ν) ≤
      Real.sqrt K*Real.exp (-c*(n+2 : ℕ))*M := by
    rw [integral_div] at hTail
    exact (div_le_iff₀ hM).mp (hTail.trans
      (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg K)))
  have hcoef : (n+1 : ℝ)/(a*ρ) ≤ (2/g)*(n+2 : ℕ) := by
    have ha2 : a^2=b*(n+1 : ℝ)/(n+2 : ℕ) := scaleFactor_square n (by omega) hb.le
    have hscale : a ≤ Real.sqrt b := scaleFactor_le_sqrt (by omega) (by omega) hb.le
    have hs : (Real.sqrt b)^2=b := Real.sq_sqrt hb.le
    have hEq : (n+1 : ℝ)/(a*ρ)=(2/g)*(n+2 : ℕ)*(a/Real.sqrt b) := by
      dsimp only [ρ]
      have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp at ha2 ⊢
      nlinarith
    rw [hEq]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (Real.sqrt_pos.mpr hb)).mpr hscale)
  have hDom : (∫ W in (maximumEvent n k)ᶜ, |(k • 1-W).adjugate.trace| ∂ν) ≤
      (n+1 : ℝ)/(a*ρ)*(∫ W in (maximumEvent n k)ᶜ, matrixClippedDet n k (a*ρ) W ∂ν) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hI.abs.integrableOn
      (((clippedDet_integrable n (n+2) (by omega) hb (mul_pos ha hρ) k).const_mul _).integrableOn)
    filter_upwards [ae_restrict_of_ae (goe_symmetric_ae (n+1) (n+2) b)] with W hW
    exact adjugate_abs_le_clipped n k (mul_pos ha hρ) W hW
  rw [hdiff]
  have hhalf := (hcomp k hk).1
  calc
    _ ≤ ∫ W in (maximumEvent n k)ᶜ, |(k • 1-W).adjugate.trace| ∂ν := abs_integral_le_integral_abs
    _ ≤ _ := hDom
    _ ≤ ((2/g)*(n+2 : ℕ))*(Real.sqrt K*Real.exp (-c*(n+2 : ℕ))*M) :=
      mul_le_mul hcoef hClip (integral_nonneg (fun W => (matrixClippedDet_pos n k (a*ρ) W).le)) (by positivity)
    _ ≤ (4/g)*Real.sqrt K*(n+2 : ℕ)*Real.exp (-c*(n+2 : ℕ))*maximumMean n (n+2) b k := by
      have hh := mul_le_mul_of_nonneg_left hhalf
        (show 0 ≤ (4/g)*Real.sqrt K*(n+2 : ℕ)*Real.exp (-c*(n+2 : ℕ)) by positivity)
      convert hh using 1
      dsimp only [M]
      ring


private lemma signed_normalized_slope_bound (n : ℕ) {b g k : ℝ}
    (hb : 0<b) (hg : 0<g) (hk : 2*Real.sqrt b+g ≤ k) :
    |((n+1 : ℝ)*signedPhysicalMean n (n+2) b k/
      signedPhysicalMean (n+1) (n+2) b k)/(n+2 : ℕ)| ≤ 1/g := by
  let a := scaleFactor n (n+2) b
  let s := k/a-2
  have ha : 0<a := scaleFactor_pos n (by omega) hb
  have hscale : a ≤ Real.sqrt b := scaleFactor_le_sqrt (by omega) (by omega) hb.le
  have hka : 2*a<k := by linarith
  have hs : 0<s := by dsimp [s]; have hh := (lt_div_iff₀ ha).mpr hka; linarith
  have hgap : g ≤ a*s := by dsimp [s]; field_simp; nlinarith
  have hj : 0 ≤ GOELogPotential.jacobiNormalizedResolvent n s := by
    rw [JacobiPrefactors.normalized_resolvent_eq_empirical]
    exact (OAI.CriticalSK.empiricalResolvent_pos _ (OAI.CriticalSK.jacobiGaps_nonneg _) hs).le
  have hjup : GOELogPotential.jacobiNormalizedResolvent n s ≤ s⁻¹ := by
    rw [JacobiPrefactors.normalized_resolvent_eq_empirical]
    exact OAI.CriticalSK.empiricalResolvent_le_inv _ (OAI.CriticalSK.jacobiGaps_nonneg _) hs
  have hja : GOELogPotential.jacobiNormalizedResolvent n s/a ≤ 1/g := by
    calc
      _ ≤ s⁻¹/a := div_le_div_of_nonneg_right hjup ha.le
      _ = 1/(a*s) := by ring_nf
      _ ≤ 1/g := one_div_le_one_div_of_le hg hgap
  have hratio : (n+1 : ℝ)/(n+2 : ℕ) ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<(n+2 : ℕ))).mpr
    push_cast; linarith
  rw [mul_div_assoc, signedPhysicalMean_ratio_eq_jacobi n (by omega) hb hka]
  have he : (n+1 : ℝ)*(GOELogPotential.jacobiNormalizedResolvent n s/a)/(n+2 : ℕ)=
      ((n+1 : ℝ)/(n+2 : ℕ))*(GOELogPotential.jacobiNormalizedResolvent n s/a) := by ring_nf
  change |(n+1 : ℝ)*(GOELogPotential.jacobiNormalizedResolvent n s/a)/(n+2 : ℕ)| ≤ _
  rw [he,abs_of_nonneg (by positivity : 0 ≤ ((n+1 : ℝ)/(n+2 : ℕ))*(GOELogPotential.jacobiNormalizedResolvent n s/a))]
  exact (mul_le_mul_of_nonneg_right hratio (div_nonneg hj ha.le)).trans (by simpa using hja)


/-- The actual restricted adjugate-to-determinant ratio has the same
normalized slope as the signed characteristic polynomial, with exponential
error. This comparison does not infer derivative control from close means:
both the determinant and the adjugate errors are used. -/
private theorem maximum_normalized_slope_signed_error {b g Z : ℝ} (hb : 0<b) (hg : 0<g) :
    ∃ C c : ℝ, 0<C ∧ 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      |(maximumAdjugateMean n (n+2) b k/maximumMean n (n+2) b k)/(n+2 : ℕ)-
        ((n+1 : ℝ)*signedPhysicalMean n (n+2) b k/
          signedPhysicalMean (n+1) (n+2) b k)/(n+2 : ℕ)| ≤ C*Real.exp (-c*(n+2 : ℕ)) := by
  obtain ⟨C₁,c₁,hC₁,hc₁,hAdj⟩ := excluded_adjugate_relative_loss (Z := Z) hb hg
  obtain ⟨C₂,c₂,hC₂,hc₂,hDet⟩ := signedPhysicalMean_maximumMean_relative_loss (Z := Z) hb hg
  refine ⟨C₁+C₂/g,min c₁ c₂,by positivity,lt_min hc₁ hc₂,?_⟩
  filter_upwards [hAdj,hDet] with n hA hD
  intro k hk
  let P := signedPhysicalMean (n+1) (n+2) b k
  let D := maximumMean n (n+2) b k
  let A := (n+1 : ℝ)*signedPhysicalMean n (n+2) b k
  let B := maximumAdjugateMean n (n+2) b k
  let E := Real.exp (-min c₁ c₂*(n+2 : ℕ))
  have hN : (0:ℝ)<(n+2 : ℕ) := by positivity
  have hEdge : 2*Real.sqrt b<k := by linarith [hk.1]
  have hP : 0<P := signedPhysicalMean_pos n (by omega) (by omega) hb hEdge
  have hDpos : 0<D := maximumMean_pos_all_dimensions n (by omega) hb
    (lt_of_le_of_lt (by positivity : (0:ℝ) ≤ 2*Real.sqrt b) hEdge)
  have he₁ : Real.exp (-c₁*(n+2 : ℕ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hN.le
    linarith
  have he₂ : Real.exp (-c₂*(n+2 : ℕ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hN.le
    linarith
  have hBA : |B-A|/(D*(n+2 : ℕ)) ≤ C₁*E := by
    apply (div_le_iff₀ (mul_pos hDpos hN)).mpr
    have hh := (hA k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he₁ (show 0 ≤ C₁*(n+2 : ℕ) by positivity)) hDpos.le)
    rw [abs_sub_comm] at hh
    simpa only [A,B,D,mul_assoc,mul_comm,mul_left_comm] using hh
  have hPD : |P-D|/D ≤ C₂*E := by
    apply (div_le_iff₀ hDpos).mpr
    exact (hD k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he₂ hC₂.le) hDpos.le)
  have hSlope : |A/P/(n+2 : ℕ)| ≤ 1/g := signed_normalized_slope_bound n hb hg hk.1
  have heq : B/D/(n+2 : ℕ)-A/P/(n+2 : ℕ)=
      (B-A)/(D*(n+2 : ℕ))+(A/P/(n+2 : ℕ))*((P-D)/D) := by
    field_simp [hP.ne',hDpos.ne',hN.ne']; ring
  change |B/D/(n+2 : ℕ)-A/P/(n+2 : ℕ)| ≤ (C₁+C₂/g)*E
  rw [heq]
  calc
    _ ≤ |(B-A)/(D*(n+2 : ℕ))|+|A/P/(n+2 : ℕ)| * |(P-D)/D| := by
      simpa only [abs_mul] using abs_add_le ((B-A)/(D*(n+2 : ℕ))) ((A/P/(n+2 : ℕ))*((P-D)/D))
    _ = |B-A|/(D*(n+2 : ℕ))+|A/P/(n+2 : ℕ)| * (|P-D|/D) := by
      rw [abs_div (B-A) (D*(n+2 : ℕ)),abs_of_pos (mul_pos hDpos hN),abs_div (P-D) D,abs_of_pos hDpos]
    _ ≤ C₁*E+(1/g)*(C₂*E) := add_le_add hBA
      (mul_le_mul hSlope hPD (div_nonneg (abs_nonneg _) hDpos.le) (by positivity))
    _ = _ := by ring


/-- Inverse-dimension accuracy for the actual maximum determinant's
logarithmic slope, uniformly on every compact interval above the edge. -/
private theorem maximumMean_log_slope_rate (hGOE : GOENoFixedTopEigenvalue)
    {b g Z : ℝ} (hb : 0<b) (hg : 0<g) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      |deriv (fun t => Real.log (maximumMean n (n+2) b t)) k/(n+2 : ℕ)-
        GOEClippedResolvent.physicalResolvent b k| ≤ C/(n+2 : ℕ) := by
  obtain ⟨C,c,hC,hc,hError⟩ := maximum_normalized_slope_signed_error (Z := Z) hb hg
  let K := (1/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g)
  have hK : 0<K := by dsimp [K]; positivity
  have hzero : Tendsto (fun n : ℕ => (n+2 : ℕ)*Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (0:ℝ)) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) c hc).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)) using 1
    funext n; simp only [Function.comp_apply,Real.rpow_one]
  refine ⟨C+2*K,by positivity,?_⟩
  filter_upwards [hError,hzero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn hsmall
  intro k hk
  have hN : (0:ℝ)<(n+2 : ℕ) := by positivity
  have hEdge : 2*Real.sqrt b<k := by linarith [hk.1]
  have hMax : 0 < maximumMean n (n+2) b k := maximumMean_pos_all_dimensions n (by omega) hb
    (lt_of_le_of_lt (by positivity : (0:ℝ) ≤ 2*Real.sqrt b) hEdge)
  rw [((maximumMean_hasDerivAt hGOE n (n+2) (by omega) hb k).log hMax.ne').deriv]
  have hRate := GOEPureSignedPhysicalSlopeRate.signed_physical_energy_slope_rate n hb hg
    (by norm_num : (0:ℝ) ≤ 1) hk.1
  have hSigned := (signedPhysicalMean_log_hasDerivAt_jacobi n (n+2) (by omega) (by omega) hb hEdge).deriv
  have hSigned' := (signedPhysicalMean_log_hasDerivAt n (n+2) (by omega) (by omega) hb hEdge).deriv
  have hEq := hSigned'.symm.trans hSigned
  simp only [one_mul] at hRate
  have hRate0 : |((n+1 : ℝ)*signedPhysicalMean n (n+2) b k/
        signedPhysicalMean (n+1) (n+2) b k)/(n+2 : ℕ)-
      GOEClippedResolvent.physicalResolvent b k| ≤ K/(n+1 : ℝ) := by
    rw [hEq]
    convert hRate using 1
    congr 1
    push_cast
    ring
  have hRate' : |((n+1 : ℝ)*signedPhysicalMean n (n+2) b k/
        signedPhysicalMean (n+1) (n+2) b k)/(n+2 : ℕ)-
      GOEClippedResolvent.physicalResolvent b k| ≤ 2*K/(n+2 : ℕ) := by
    have hDen : K/(n+1 : ℝ) ≤ 2*K/(n+2 : ℕ) := by
      apply (div_le_div_iff₀ (by positivity : (0:ℝ)<n+1) hN).mpr
      push_cast; nlinarith
    exact hRate0.trans hDen
  have hExp : C*Real.exp (-c*(n+2 : ℕ)) ≤ C/(n+2 : ℕ) := by
    apply (le_div_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall.le hC.le
    nlinarith
  calc
    _ ≤ |maximumAdjugateMean n (n+2) b k/maximumMean n (n+2) b k/(n+2 : ℕ)-
          ((n+1 : ℝ)*signedPhysicalMean n (n+2) b k/signedPhysicalMean (n+1) (n+2) b k)/(n+2 : ℕ)|+
        |((n+1 : ℝ)*signedPhysicalMean n (n+2) b k/signedPhysicalMean (n+1) (n+2) b k)/(n+2 : ℕ)-
          GOEClippedResolvent.physicalResolvent b k| := abs_sub_le _ _ _
    _ ≤ C*Real.exp (-c*(n+2 : ℕ))+2*K/(n+2 : ℕ) := add_le_add (hn k hk) hRate'
    _ ≤ C/(n+2 : ℕ)+2*K/(n+2 : ℕ) := add_le_add hExp le_rfl
    _ = (C+2*K)/(n+2 : ℕ) := by ring

private lemma pureMaximum_log_decomposition (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0<a) {Q : ℝ} (hQ : 0<Q) (H : ℝ)
    (hk : 0 < (p : ℝ)*H/(n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal=
      Real.log (((n+2 : ℕ) : ℝ)⁻¹)+Real.log (sphereKRPrefactor (n+1) μ Q).toReal+
        (Real.log (n+2 : ℕ)-Real.log (2*Real.pi*μ.xi Q))/2-
          H^2/(2*(n+2 : ℕ)*μ.xi Q)+
            Real.log (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p : ℝ)*H/(n+2 : ℕ))) := by
  let μ := FiniteMixture.pure p hp a ha
  have hN : (0:ℝ)<(n+2 : ℕ) := by positivity
  have hb : 0<Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hm := maximumMean_pos_all_dimensions n (N := n+2) (by omega) hb hk
  have hs : 0<(sphereKRPrefactor (n+1) μ Q).toReal :=
    ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ) (sphereKRPrefactor_ne_top (n+1) μ Q)
  have hd := physicalValuePdf_toReal_pos (n+2) (by omega) μ hQ (H/(n+2 : ℕ))
  have harg : (p : ℝ)*(H/(n+2 : ℕ))=(p : ℝ)*H/(n+2 : ℕ) := by ring
  unfold pureLocalMaxPhysicalIntensity pureNegativeIntensity
  dsimp only
  rw [harg,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le),ENNReal.toReal_ofReal hm.le,
    Real.log_mul (inv_pos.mpr hN).ne' (mul_pos (mul_pos hs hd) hm).ne',
    Real.log_mul (mul_pos hs hd).ne' hm.ne',Real.log_mul hs.ne' hd.ne',
    physicalValuePdf_log (n+2) (by omega) μ hQ]
  have hGauss : (n+2 : ℕ)*(H/(n+2 : ℕ))^2/(2*μ.xi Q)=H^2/(2*(n+2 : ℕ)*μ.xi Q) := by
    field_simp
  rw [hGauss]
  ring


/-- Exact logarithmic energy derivative of the genuine pure local-maximum
Kac--Rice intensity, with its physical-energy Jacobian and scalar Gaussian
density. This is equation `mo-pure-slope`, for the actual restricted mean. -/
private theorem pureLocalMaxPhysicalIntensity_log_hasDerivAt (hGOE : GOENoFixedTopEigenvalue)
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) {Q : ℝ} (hQ : 0<Q) (H : ℝ)
    (hk : 0 < (p : ℝ)*H/(n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let b := Q^2*μ.xi2 Q
    HasDerivAt (fun t => Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q t).toReal)
      (-H/((n+2 : ℕ)*μ.xi Q)+(p : ℝ)/(n+2 : ℕ)*
        (maximumAdjugateMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ))/
          maximumMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ)))) H := by
  let μ := FiniteMixture.pure p hp a ha
  let b := Q^2*μ.xi2 Q
  have hb : 0<b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hN : (0:ℝ)<(n+2 : ℕ) := by positivity
  have hm := maximumMean_pos_all_dimensions n (N := n+2) (by omega) hb hk
  have hArg : HasDerivAt (fun t : ℝ => (p : ℝ)*t/(n+2 : ℕ)) ((p : ℝ)/(n+2 : ℕ)) H :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id H).const_mul (p : ℝ)).div_const ((n+2 : ℕ) : ℝ)
  have hDet := ((maximumMean_hasDerivAt hGOE n (n+2) (by omega) hb _).log hm.ne').comp H hArg
  have hGauss : HasDerivAt (fun t : ℝ => -t^2/(2*(n+2 : ℕ)*μ.xi Q))
      (-H/((n+2 : ℕ)*μ.xi Q)) H := by
    convert (((hasDerivAt_id H).pow 2).neg).div_const (2*(n+2 : ℕ)*μ.xi Q) using 1
    · funext t; rfl
    · dsimp; field_simp
  let A := Real.log (((n+2 : ℕ) : ℝ)⁻¹)+Real.log (sphereKRPrefactor (n+1) μ Q).toReal+
    (Real.log (n+2 : ℕ)-Real.log (2*Real.pi*μ.xi Q))/2
  have hd := (hGauss.const_add A).add hDet
  have heq : (fun t => Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q t).toReal) =ᶠ[𝓝 H]
      (fun t => A+-t^2/(2*(n+2 : ℕ)*μ.xi Q)+Real.log (maximumMean n (n+2) b ((p : ℝ)*t/(n+2 : ℕ)))) := by
    have hpos := hArg.continuousAt (Ioi_mem_nhds hk)
    filter_upwards [hpos] with t ht
    have he := pureMaximum_log_decomposition n p hp a ha hQ t ht
    simpa only [A,μ,b,sub_eq_add_neg,neg_div] using he
  convert hd.congr_of_eventuallyEq heq using 1
  ring


/-- Manuscript `prop:mo-pure` (b), uniformly on any fixed exterior mark
interval, for the actual negative-Hessian intensity and the literal scalar
complexity. The error is `C/N` in unnormalized energy. -/
theorem pureLocalMaxPhysicalIntensity_log_slope_rate (hGOE : GOENoFixedTopEigenvalue)
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) {Q : ℝ} (hQ : 0<Q)
    {g Z : ℝ} (hg : 0<g) :
    let μ := FiniteMixture.pure p hp a ha
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ,
      (p : ℝ)*H/(n+2 : ℕ) ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z →
      |deriv (fun t => Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q t).toReal) H-
        deriv (pureMarkedComplexity p hp a ha Q) (H/(n+2 : ℕ))| ≤ C/(n+2 : ℕ) := by
  let μ := FiniteMixture.pure p hp a ha
  let b := Q^2*μ.xi2 Q
  have hb : 0<b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hpR : 0<(p : ℝ) := by exact_mod_cast (show 0<p by omega)
  obtain ⟨C,hC,hRate⟩ := maximumMean_log_slope_rate hGOE (Z := Z) hb hg
  refine ⟨(p : ℝ)*C,by positivity,?_⟩
  filter_upwards [hRate] with n hn
  intro H hH
  have hEdge : 2*Real.sqrt b<(p : ℝ)*H/(n+2 : ℕ) := by linarith [hH.1]
  have hk : 0<(p : ℝ)*H/(n+2 : ℕ) := (by positivity : (0:ℝ) ≤ 2*Real.sqrt b).trans_lt hEdge
  rw [(pureLocalMaxPhysicalIntensity_log_hasDerivAt hGOE n p hp a ha hQ H hk).deriv]
  have hEdge' : 2*Real.sqrt b<(p : ℝ)*(H/(n+2 : ℕ)) := by convert hEdge using 1; ring
  rw [(sourcePureComplexity_hasDerivAt p hp a ha hQ _ hEdge').deriv]
  have hOmega : 2<(p : ℝ)*(H/(n+2 : ℕ))/Real.sqrt b :=
    (lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hEdge'
  have hScore : sourcePureComplexityDerivative p hp a ha Q (H/(n+2 : ℕ))=
      -H/((n+2 : ℕ)*μ.xi Q)+(p : ℝ)*GOEClippedResolvent.physicalResolvent b ((p : ℝ)*H/(n+2 : ℕ)) := by
    unfold sourcePureComplexityDerivative
    rw [SemicirclePotential.resolvent_eq_semicircleResolvent hOmega]
    unfold GOEClippedResolvent.physicalResolvent
    dsimp only [b,μ]
    ring_nf
  rw [hScore]
  have hh := hn _ hH
  rw [((maximumMean_hasDerivAt hGOE n (n+2) (by omega) hb _).log
    (maximumMean_pos_all_dimensions n (by omega) hb hk).ne').deriv] at hh
  have heq : -H/((n+2 : ℕ)*(FiniteMixture.pure p hp a ha).xi Q)+
      (p : ℝ)/(n+2 : ℕ)*(maximumAdjugateMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ))/
        maximumMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ)))-
      (-H/((n+2 : ℕ)*μ.xi Q)+(p : ℝ)*GOEClippedResolvent.physicalResolvent b ((p : ℝ)*H/(n+2 : ℕ)))=
      (p : ℝ)*(maximumAdjugateMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ))/
        maximumMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ))/(n+2 : ℕ)-
          GOEClippedResolvent.physicalResolvent b ((p : ℝ)*H/(n+2 : ℕ))) := by
    dsimp only [μ]; ring
  change |(-H/((n+2 : ℕ)*(FiniteMixture.pure p hp a ha).xi Q)+
      (p : ℝ)/(n+2 : ℕ)*(maximumAdjugateMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ))/
        maximumMean n (n+2) b ((p : ℝ)*H/(n+2 : ℕ))))-_| ≤ _
  rw [heq,abs_mul,abs_of_pos hpR]
  exact (mul_le_mul_of_nonneg_left hh hpR.le).trans_eq (by ring)

/-- The manuscript's radially truncated scalar intensity on the graph
`k=p*h/N`. Its truncation vanishes at and outside the supplied open interval. -/
def pureGraphMaximumIntensity (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a)
    (Q : ℝ) (U : Set ℝ) (H : ℝ) : ℝ≥0∞ :=
  if (p : ℝ)*H/(n+2 : ℕ) ∈ U then pureLocalMaxPhysicalIntensity n p hp a ha Q H else 0

/-- The same `C/N` slope bound for the literal, radially truncated intensity
of `mo-pure-intensity`, uniformly at every point of its open support. -/
theorem pureGraphMaximumIntensity_log_slope_rate (hGOE : GOENoFixedTopEigenvalue)
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) {Q : ℝ} (hQ : 0<Q)
    (U : Set ℝ) (hU : IsOpen U) {g Z : ℝ} (hg : 0<g)
    (hgap : U ⊆ Icc (2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g) Z) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ, (p : ℝ)*H/(n+2 : ℕ) ∈ U →
      |deriv (fun t => Real.log (pureGraphMaximumIntensity n p hp a ha Q U t).toReal) H-
        deriv (pureMarkedComplexity p hp a ha Q) (H/(n+2 : ℕ))| ≤ C/(n+2 : ℕ) := by
  obtain ⟨C,hC,hRate⟩ := pureLocalMaxPhysicalIntensity_log_slope_rate hGOE p hp a ha hQ (Z := Z) hg
  refine ⟨C,hC,?_⟩
  filter_upwards [hRate] with n hn
  intro H hH
  have heq : (fun t => Real.log (pureGraphMaximumIntensity n p hp a ha Q U t).toReal) =ᶠ[𝓝 H]
      (fun t => Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q t).toReal) := by
    have hc : Continuous (fun t : ℝ => (p : ℝ)*t/(n+2 : ℕ)) := by fun_prop
    filter_upwards [hc.continuousAt (hU.mem_nhds hH)] with t ht
    change (p : ℝ)*t/(n+2 : ℕ) ∈ U at ht
    simp only [pureGraphMaximumIntensity,ite_eq_left ht]
  rw [heq.deriv_eq]
  exact hn H (hgap hH)

/-- The literal radial truncation on the Euler graph equals the energy
truncation used to construct the normalized center. Thus its tail equals one
at exactly the same center, with no asymptotic identification of centers. -/
theorem pureGraphMaximumIntensity_eq_truncated (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0<a) (Q l r H : ℝ) :
    (pureGraphMaximumIntensity n p hp a ha Q (Ioo ((p : ℝ)*l) ((p : ℝ)*r)) H).toReal=
      pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H := by
  have hpR : 0<(p : ℝ) := by exact_mod_cast (show 0<p by omega)
  have hN : (0:ℝ)<(n+2 : ℕ) := by positivity
  have harg : (p : ℝ)*H/(n+2 : ℕ)=(p : ℝ)*(H/(n+2 : ℕ)) := by ring
  have hmem : (p : ℝ)*H/(n+2 : ℕ) ∈ Ioo ((p : ℝ)*l) ((p : ℝ)*r) ↔
      H ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) := by
    rw [harg]
    constructor
    · intro hH
      have hl := lt_of_mul_lt_mul_left hH.1 hpR.le
      have hr := lt_of_mul_lt_mul_left hH.2 hpR.le
      have hl' := (lt_div_iff₀ hN).mp hl
      have hr' := (div_lt_iff₀ hN).mp hr
      constructor <;> nlinarith
    · intro hH
      have hl : l<H/(n+2 : ℕ) := (lt_div_iff₀ hN).mpr (by nlinarith [hH.1])
      have hr : H/(n+2 : ℕ)<r := (div_lt_iff₀ hN).mpr (by nlinarith [hH.2])
      exact ⟨mul_lt_mul_of_pos_left hl hpR,mul_lt_mul_of_pos_left hr hpR⟩
  by_cases hH : H ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  · simp only [pureGraphMaximumIntensity,ite_eq_left (hmem.mpr hH),
      pureTruncatedLocalMaxDensity,indicator_of_mem hH]
  · simp only [pureGraphMaximumIntensity,ite_eq_right (fun ht => hH (hmem.mp ht)),
      ENNReal.toReal_zero,pureTruncatedLocalMaxDensity,indicator_of_notMem hH]

/-- The scalar graph map in raw energy and normalized radial coordinates. -/
def purePhysicalGraph (n p : ℕ) (H : ℝ) : ℝ × ℝ :=
  (H,(p : ℝ)*H/(n+2 : ℕ))

/-- The inverse image of a raw-energy/radial Borel set in normalized score
coordinates. Unlike a two-dimensional score density, this remains meaningful
for a pure covariance. -/
def purePhysicalScoreSet (n : ℕ) (A : Set (ℝ × ℝ)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | ((n+2 : ℕ)*z 0,z 1) ∈ A}

/-- The singular expected-count law is literally the pushforward of its
one-dimensional physical energy density onto the Euler graph. -/
def pureMaximumCountMeasure (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) (Q : ℝ) :
    Measure (ℝ × ℝ) :=
  (volume.withDensity (pureLocalMaxPhysicalIntensity n p hp a ha Q)).map (purePhysicalGraph n p)

/-- The all-critical counterpart of the same singular graph law. -/
def pureCriticalCountMeasure (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) (Q : ℝ) :
    Measure (ℝ × ℝ) :=
  (volume.withDensity (pureCriticalPhysicalIntensity n p hp a ha Q)).map (purePhysicalGraph n p)

private lemma pureScoreSet_rescale (n p : ℕ) (A : Set (ℝ × ℝ)) :
    pureScoreWindow p (purePhysicalScoreSet n A)=
      (fun e : ℝ => ((n+2 : ℕ) : ℝ)*e) ⁻¹' (purePhysicalGraph n p ⁻¹' A) := by
  ext e
  have he : (p : ℝ)*((n+2 : ℕ)*e)/(n+2 : ℕ)=(p : ℝ)*e := by field_simp
  change (((n+2 : ℕ) : ℝ)*e,(p : ℝ)*e) ∈ A ↔
    (((n+2 : ℕ) : ℝ)*e,(p : ℝ)*((n+2 : ℕ)*e)/(n+2 : ℕ)) ∈ A
  rw [he]


/-- Exact expected counts on every Borel subset of the raw energy/radial
plane, for both all critical points and local maxima. This identifies the
singular joint measures printed in `prop:mo-pure` (a), including their full
physical Jacobian. Radial truncation is obtained by intersecting `A` with
`univ ×ˢ U`. -/
theorem pure_physical_graph_count_laws (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a)
    {Q : ℝ} (hQ : 0<Q) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c (purePhysicalScoreSet n A) (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree)=pureCriticalCountMeasure n p hp a ha Q A ∧
    (∫⁻ J, actualLocalMaxCount (n+1) c (purePhysicalScoreSet n A) J
      ∂disorderLaw (n+2) μ.maxDegree)=pureMaximumCountMeasure n p hp a ha Q A := by
  have hK : MeasurableSet (purePhysicalScoreSet n A) := by
    exact hA.preimage (by fun_prop)
  have hg : Measurable (purePhysicalGraph n p) := by unfold purePhysicalGraph; fun_prop
  have hc := actual_pure_count_intensity n p hp a ha hQ _ hK
  have hm := (actual_pure_localMax_count_intensity n p hp a ha hQ _ hK).2
  rw [pureScoreSet_rescale] at hc hm
  rw [setLIntegral_positive_rescale (n+2 : ℕ) (by positivity)] at hc hm
  dsimp only
  constructor
  · rw [pureCriticalCountMeasure,Measure.map_apply hg hA,withDensity_apply _ (hA.preimage hg)]
    exact hc
  · rw [pureMaximumCountMeasure,Measure.map_apply hg hA,withDensity_apply _ (hA.preimage hg)]
    exact hm

/-- The actual pure local-maximum Palm law at a fixed point and normalized
energy, as a measure of the original disorder and its deterministic radial
mark. The Hessian weight includes negativity and is normalized by the actual
restricted mean, rather than the all-critical or signed mean. -/
def pureMaximumPalm (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a)
    (Q e : ℝ) (u : Vector (n+2)) (hu : ‖u‖^2=(n+2 : ℕ)) :
    Measure (Disorder (n+2) (FiniteMixture.pure p hp a ha).maxDegree × ℝ) :=
  let μ := FiniteMixture.pure p hp a ha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  ((valueConditionedLaw c u hu e).withDensity (fun J =>
    (ENNReal.ofReal |(SphereHessian.intrinsicHessian (field c J) u).det| * 
      SphericalPosteriorMaps.negativeHessianMark (n+1) c J u)*
        (ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p : ℝ)*e)))⁻¹)).map
    (fun J => (J,(p : ℝ)*e))


/-- Normalization and the full nonnegative Borel test-function formula for
`mo-pure-palm`, including the Dirac radial mark `k=p*e`. No literature
hypothesis is needed for this identity. -/
theorem pureMaximumPalm_probability_and_formula (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0<a) {Q : ℝ} (hQ : 0<Q) (e : ℝ) (he : 0<(p : ℝ)*e)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    IsProbabilityMeasure (pureMaximumPalm n p hp a ha Q e u hu) ∧
    ∀ f : Disorder (n+2) μ.maxDegree × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂pureMaximumPalm n p hp a ha Q e u hu)=
        (∫⁻ J, ENNReal.ofReal |(SphereHessian.intrinsicHessian (field c J) u).det| * 
          SphericalPosteriorMaps.negativeHessianMark (n+1) c J u*f (J,(p : ℝ)*e)
          ∂valueConditionedLaw c u hu e)/
            ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p : ℝ)*e)) := by
  let μ := FiniteMixture.pure p hp a ha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := valueConditionedLaw c u hu e
  let D := fun J => ENNReal.ofReal |(SphereHessian.intrinsicHessian (field c J) u).det| * 
    SphericalPosteriorMaps.negativeHessianMark (n+1) c J u
  let M := ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p : ℝ)*e))
  have hD : Measurable D := (intrinsicDet_measurable c u hu).mul
    ((SphericalPosteriorMaps.negativeHessianMark_measurable (n+1) c).comp
      (measurable_id.prodMk measurable_const))
  have hM : M ≠ 0 := (ENNReal.ofReal_pos.mpr (maximumMean_pos_all_dimensions n (N := n+2) (by omega)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) he)).ne'
  have hMtop : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hMean : (∫⁻ J, D J ∂ν)=M := pure_posterior_negative_det_mean n p hp a ha hQ u hu e
  have hMap : Measurable (fun J : Disorder (n+2) μ.maxDegree => (J,(p : ℝ)*e)) := by fun_prop
  have hν : IsProbabilityMeasure (ν.withDensity (fun J => D J*M⁻¹)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      lintegral_mul_const _ hD,hMean,ENNReal.mul_inv_cancel hM hMtop]
  constructor
  · change IsProbabilityMeasure ((ν.withDensity (fun J => D J*M⁻¹)).map (fun J => (J,(p : ℝ)*e)))
    let := hν
    infer_instance
  · intro f hf
    change (∫⁻ z, f z ∂(ν.withDensity (fun J => D J*M⁻¹)).map (fun J => (J,(p : ℝ)*e)))=_
    rw [lintegral_map hf hMap]
    calc
      _ = ∫⁻ J, (D J*M⁻¹)*f (J,(p : ℝ)*e) ∂ν := by
        simpa only [Function.comp_apply,Pi.mul_apply] using
          (lintegral_withDensity_eq_lintegral_mul ν (hD.mul_const _) (hf.comp hMap))
      _ = ∫⁻ J, (D J*f (J,(p : ℝ)*e))*M⁻¹ ∂ν := by
        apply lintegral_congr
        intro J
        ac_rfl
      _ = (∫⁻ J, D J*f (J,(p : ℝ)*e) ∂ν)/M := by
        simpa only [Function.comp_apply,Pi.mul_apply,div_eq_mul_inv] using
          (lintegral_mul_const (μ := ν) M⁻¹ (hD.mul (hf.comp hMap)))


/-- The contact identities and the manuscript's global quadratic
complexity bound, including energies inside the spectral support. -/
theorem pure_complexity_contact_and_quadratic
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := TwoAtomStationarity.markE μ β x Q
    pureMarkedComplexity p hp a ha Q E=0 ∧
    HasDerivAt (pureMarkedComplexity p hp a ha Q) (-(β*x)) E ∧
    ∀ e : ℝ, pureMarkedComplexity p hp a ha Q e ≤
      -(β*x)*(e-E)-((p : ℝ)-2)/(4*((p : ℝ)-1)*μ.xi Q)*(e-E)^2 := by
  let μ := FiniteMixture.pure p hp a ha
  let E := TwoAtomStationarity.markE μ β x Q
  let b := Q^2*μ.xi2 Q
  have hb : 0<b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hV := μ.xi_pos h.overlap_range.1
  have hZero := sourcePure_contact_complexity_zero p hp a ha h
  refine ⟨hZero,sourcePure_contact_complexity_hasDerivAt p hp a ha h,?_⟩
  intro e
  have hEdge : 2<(p : ℝ)*E/Real.sqrt b := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    rw [← sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hLoss := PureScalarComplexityGeometry.profile_contact_loss hV hb hEdge hZero
    (sourcePure_contact_complexity_derivative p hp a ha h) e
  have hId : b=(p : ℝ)*((p : ℝ)-1)*μ.xi Q :=
    (sourcePure_contact_covariance_scalars p hp a ha Q).2
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hcoef : PureScalarComplexityGeometry.curvature (μ.xi Q) b (p : ℝ)/2=
      ((p : ℝ)-2)/(4*((p : ℝ)-1)*μ.xi Q) := by
    unfold PureScalarComplexityGeometry.curvature
    rw [hId]
    field_simp [hV.ne',show (p : ℝ)-1 ≠ 0 by linarith,
      show (p : ℝ) ≠ 0 by linarith]
    ring
  rw [hcoef] at hLoss
  exact hLoss


/-- One and the same exact unit-tail center gives the logarithmic centering,
density normalization, and both fixed-window and upper-tail limits for all
critical points and genuine local maxima. The interval is chosen before
all windows and dimensions. This assembles the normalization portion of
`prop:mo-pure` (c); it introduces no literature hypothesis. -/
theorem pure_onePoint_normalized_limits
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0<a) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : TwoAtomStationarity.markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0<g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := TwoAtomStationarity.markE (FiniteMixture.pure p hp a ha) β x Q
    let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    let fcrit := fun n : ℕ => sourcePureTruncatedCriticalDensity n p hp a ha Q
      ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    ∃ n₀ : ℕ, ∃ m : ℕ → ℝ, ∃ M : ℝ, 0<M ∧
      (∀ n<n₀, m n=(n+2 : ℕ)*E) ∧
      (∀ n≥n₀, ExpectedTailCentering.tail (f n) (m n)=1 ∧
        (∀ y : ℝ, ExpectedTailCentering.tail (f n) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      Tendsto (fun n => f n (m n)) atTop (𝓝 (β*x)) ∧
      (∀ t : ℝ, Tendsto (fun n => ExpectedTailCentering.tail (f n) (m n+t))
        atTop (𝓝 (Real.exp (-(β*x)*t)))) ∧
      (∀ t : ℝ, Tendsto (fun n => ExpectedTailCentering.tail (fcrit n) (m n+t))
        atTop (𝓝 (Real.exp (-(β*x)*t)))) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n =>
        sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (m n+L) (m n+R))
          atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n =>
        sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r (m n+L) (m n+R))
          atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) := by
  obtain ⟨n₀,m,M,hM,hFallback,hCenter,hCrit⟩ :=
    sourcePure_truncatedCritical_center_count_limits p hp a ha h hm hg hLeft hRight
  have hEvent : ∀ᶠ n : ℕ in atTop,
      ExpectedTailCentering.tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n)=1 ∧
      |m n-((n+2 : ℕ)*TwoAtomStationarity.markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact ⟨(hCenter n hn).1,(hCenter n hn).2.2⟩
  obtain ⟨hDensity,hTail⟩ := sourcePure_truncatedLocalMax_normalized_limits_of_center
    p hp a ha h hm hg hLeft hRight m hM hEvent
  have hCritTail := sourcePure_truncatedCritical_normalized_tail_limit_of_center
    p hp a ha h hm hg hLeft hRight m hM hEvent
  refine ⟨n₀,m,M,hM,hFallback,hCenter,hDensity,hTail,hCritTail,?_,hCrit⟩
  intro L R hLR
  have hi := pureTruncatedLocalMaxDensity_integrable_eventually
    p hp a ha h (hm.1.trans hm.2) hg hLeft hRight
  have hw := compact_centered_window_integral_limit m hi hTail hLR
  apply hw.congr'
  filter_upwards [] with n
  exact (sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha h.overlap_range.1
    l r (m n+L) (m n+R)).symm

end SlowEquilibration.SourcePureDeterminantDerivative
