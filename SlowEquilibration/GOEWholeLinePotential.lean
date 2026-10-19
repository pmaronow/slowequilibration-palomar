-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEWholeLineClipping
public import SlowEquilibration.SemicircleClipping
public import SlowEquilibration.UniformLipschitzConvergence
public import SlowEquilibration.GOEPrefactors
public import SlowEquilibration.GOEAllShiftPositivity

/-! Actual full-line GOE determinant exponent upper bounds. The expectation
of the clipped logarithm converges to its actual semicircle integral. Clipping
is removed uniformly on compact shifts, while genuine Gaussian MGF control
and raw determinant domination transfer the upper estimate to the ordinary
expected absolute determinant. -/

@[expose] public section
namespace SlowEquilibration.GOEWholeLinePotential

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
open GOEAsymptotics GOEClippedDeterminants GOEPrefactors GOESharpMoments
open SemicirclePotential SemicircleClipping SpectralTraceLipschitz
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def expectedClipped (n : ℕ) (k rho : ℝ) : ℝ :=
  ∫ A,clippedTrace n k rho A/(n+1 : ℝ) ∂stdGaussian (GaussianMatrix (n+1))

lemma expectedClipped_eq (n : ℕ) (k rho : ℝ) :
    expectedClipped n k rho=∫ A,GOEWholeLineClipping.normalizedClippedLog n (k-2) rho A
      ∂stdGaussian (GaussianMatrix (n+1)) := by
  simp only [expectedClipped,GOEWholeLineClipping.normalizedClippedLog,show 2+(k-2)=k by ring]

lemma expectedClipped_tendsto (k : ℝ) {rho : ℝ} (hrho : 0<rho) :
    Tendsto (fun n => expectedClipped n k rho) atTop (𝓝 (clippedPotential k rho)) := by
  have h1 := GOEWholeLineClipping.expected_normalized_clipped_log_minus_jacobi_tendsto
    (s := k-2) hrho
  have h2 := JacobiSemicircle.continuous_test_tendsto_real (clippedLog k rho)
    (clippedLog_lipschitz k hrho).continuous
  have he (n : ℕ) : GOEWholeLineClipping.jacobiNormalizedLog n (k-2) rho=
      (∑ i,clippedLog k rho (2-OAI.CriticalSK.orderedJacobiGaps n i))/(n+1 : ℝ) := by
    simp only [GOEWholeLineClipping.jacobiNormalizedLog,show 2+(k-2)=k by ring]
  have hh := h1.add h2
  simp only [← he,sub_add_cancel,zero_add,← expectedClipped_eq] at hh
  exact hh

lemma clippedLog_shift_dist {rho : ℝ} (hrho : 0<rho) (k l t : ℝ) :
    |clippedLog k rho t-clippedLog l rho t|≤(1/rho)*|k-l| := by
  have h := (clippedLog_lipschitz t hrho).dist_le_mul k l
  simp only [Real.dist_eq] at h
  change |clippedLog t rho k-clippedLog t rho l|≤(1/rho)*|k-l| at h
  simpa only [clippedLog,abs_sub_comm t k,abs_sub_comm t l] using h

lemma normalizedTrace_shift_dist (n : ℕ) {rho : ℝ} (hrho : 0<rho) (k l : ℝ)
    (A : GaussianMatrix (n+1)) :
    |clippedTrace n k rho A/(n+1 : ℝ)-clippedTrace n l rho A/(n+1 : ℝ)|≤(1/rho)*|k-l| := by
  unfold clippedTrace
  rw [← sub_div,← Finset.sum_sub_distrib,abs_div,
    abs_of_pos (by positivity : 0<(n+1 : ℝ))]
  apply (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mpr
  calc
    _≤∑ i,|clippedLog k rho (GOEEdgeConcentration.realizedEigenvalues n A i)-
      clippedLog l rho (GOEEdgeConcentration.realizedEigenvalues n A i)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ _i : Fin (n+1),(1/rho)*|k-l| := Finset.sum_le_sum fun i _ => clippedLog_shift_dist hrho k l _
    _=_ := by simp;ring

lemma expectedClipped_lipschitz (n : ℕ) {rho : ℝ} (hrho : 0<rho) :
    LipschitzWith ⟨1/rho,by positivity⟩ (fun k => expectedClipped n k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro k l
  rw [Real.dist_eq]
  change ‖expectedClipped n k rho-expectedClipped n l rho‖≤(1/rho)*|k-l|
  unfold expectedClipped
  rw [← integral_sub ((clippedTrace_integrable n k hrho).div_const _)
    ((clippedTrace_integrable n l hrho).div_const _)]
  have h := norm_integral_le_of_norm_le_const (μ := stdGaussian (GaussianMatrix (n+1)))
    (f := fun A => clippedTrace n k rho A/(n+1 : ℝ)-clippedTrace n l rho A/(n+1 : ℝ))
    (C := (1/rho)*|k-l|) (ae_of_all _ fun A => by
      simpa only [Real.norm_eq_abs] using normalizedTrace_shift_dist n hrho k l A)
  simpa only [probReal_univ,mul_one] using h

lemma clippedPotential_lipschitz {rho : ℝ} (hrho : 0<rho) :
    LipschitzWith ⟨1/rho,by positivity⟩ (fun k => clippedPotential k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro k l
  have ht := (expectedClipped_tendsto k hrho).dist (expectedClipped_tendsto l hrho)
  exact le_of_tendsto ht (Eventually.of_forall fun n =>
    (expectedClipped_lipschitz n hrho).dist_le_mul k l)

/-- Compact-uniform convergence of actual normalized expected clipped GOE
logdet to the literal clipped semicircle integral, valid at every real shift. -/
theorem expectedClipped_uniform {rho : ℝ} (hrho : 0<rho) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n k => expectedClipped n k rho)
      (fun k => clippedPotential k rho) atTop S :=
  UniformLipschitzConvergence.uniform_on_compact (L := ⟨1/rho,by positivity⟩) (by change (0:ℝ)<1/rho;positivity)
    (fun n => expectedClipped_lipschitz n hrho) (clippedPotential_lipschitz hrho)
    (fun k => expectedClipped_tendsto k hrho) hS

lemma matrix_mean_eq (n : ℕ) (k : ℝ) :
    (∫ W,matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)=meanAbsolute n k := by
  rw [← GOEDeterminantMoments.realization_law n,
    integral_map (GOEDeterminantMoments.realization_measurable n).aemeasurable
      (matrixAbsoluteDet_measurable n k).aestronglyMeasurable]
  rfl

lemma meanAbsolute_all_shift_pos (n : ℕ) (k : ℝ) : 0 < meanAbsolute n k := by
  have h := GOEAllShiftPositivity.abs_determinant_mean_pos (n+1) (N := n+1) (by omega) (by norm_num : (0:ℝ)<1) k
  have he : (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => |(W-k • 1).det|)=matrixAbsoluteDet n k := by
    funext W
    unfold matrixAbsoluteDet
    rw [show W-k • 1=-(k • 1-W) by abel,Matrix.det_neg,abs_mul]
    simp
  rw [he,matrix_mean_eq] at h
  exact h

lemma log_mean_upper_clipped (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0<rho) :
    Real.log (meanAbsolute n k)/(n+1 : ℝ)≤expectedClipped n k rho+1/(rho^2*(n+1 : ℝ)) := by
  let μ := stdGaussian (GaussianMatrix (n+1))
  let Y := clippedTrace n k rho
  let m := ∫ A,Y A ∂μ
  have hG := clippedTrace_centered_sharpGaussian n k hrho
  have hExp : Integrable (fun A => Real.exp (Y A)) μ := by
    apply ((hG.integrable_exp_mul 1).mul_const (Real.exp m)).congr
    exact ae_of_all μ fun A => by
      simp only [one_mul]
      rw [← Real.exp_add]
      congr 1
      dsimp only [Y,m,μ]
      ring
  have hi : meanAbsolute n k≤∫ A,Real.exp (Y A) ∂μ :=
    integral_mono (absolute_integrable n k) hExp (absoluteDet_le_exp_clippedTrace n k hrho)
  have hmgf := hG.mgf_le 1
  simp only [mgf,one_mul,one_pow,mul_one] at hmgf
  have hupper : meanAbsolute n k≤Real.exp (m+1/rho^2) := by
    apply hi.trans
    have hf : (fun A => Real.exp (Y A))=fun A => Real.exp m*Real.exp (Y A-m) := by
      funext A
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf,integral_const_mul,Real.exp_add]
    have hh := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos m).le
    rw [Real.coe_toNNReal _ (by positivity),show (2/rho^2)/2=1/rho^2 by ring] at hh
    exact hh
  have hlog := (Real.log_le_iff_le_exp (meanAbsolute_all_shift_pos n k)).mpr hupper
  have hm : expectedClipped n k rho=m/(n+1 : ℝ) := by rw [expectedClipped,integral_div]
  rw [hm]
  have hd := div_le_div_of_nonneg_right hlog (by positivity : 0≤(n+1 : ℝ))
  convert hd using 1
  rw [add_div]
  congr 1
  field_simp

/-- The genuine ordinary expected absolute GOE determinant has the literal
semicircle exponent as a compact-uniform upper limit on the whole real line. -/
theorem log_mean_upper_uniform {S : Set ℝ} (hS : IsCompact S) {eps : ℝ} (heps : 0<eps) :
    ∀ᶠ n : ℕ in atTop,∀ k∈S,
      Real.log (meanAbsolute n k)/(n+1 : ℝ)≤potential k+eps := by
  have hclip := (clippedPotential_uniform_on_compact hS) _
    (show {(x,y) : ℝ×ℝ | dist x y<eps/3}∈uniformity ℝ from by
      exact Metric.dist_mem_uniformity (by positivity))
  obtain ⟨j,hj⟩ := hclip.exists
  let rho := clippingRadius j
  have hrho : 0<rho := clippingRadius_pos j
  have hmean := (expectedClipped_uniform hrho hS) _
    (show {(x,y) : ℝ×ℝ | dist x y<eps/3}∈uniformity ℝ from by
      exact Metric.dist_mem_uniformity (by positivity))
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hsmall := ((hn.atTop_mul_const (sq_pos_of_pos hrho)).const_div_atTop 1).eventually
    (gt_mem_nhds (by positivity : 0<eps/3))
  filter_upwards [hmean,hsmall] with n hmean hsmall
  intro k hk
  have h1 := hj k hk
  have h2 := hmean k hk
  change dist (potential k) (clippedPotential k rho)<eps/3 at h1
  change dist (clippedPotential k rho) (expectedClipped n k rho)<eps/3 at h2
  simp only [Real.dist_eq] at h1 h2
  have hb := log_mean_upper_clipped n k hrho
  have hs : 1/(rho^2*(n+1 : ℝ))<eps/3 := by
    simpa only [mul_comm (rho^2)] using hsmall
  have hc : clippedPotential k rho<potential k+eps/3 := by
    linarith [(abs_lt.mp h1).1,(abs_lt.mp h1).2]
  have hm : expectedClipped n k rho<clippedPotential k rho+eps/3 := by
    linarith [(abs_lt.mp h2).1,(abs_lt.mp h2).2]
  linarith

/-- Exponential form of the same true compact-uniform all-shift bound. -/
theorem mean_upper_uniform {S : Set ℝ} (hS : IsCompact S) {eps : ℝ} (heps : 0<eps) :
    ∀ᶠ n : ℕ in atTop,∀ k∈S,
      meanAbsolute n k≤Real.exp ((n+1 : ℝ)*(potential k+eps)) := by
  filter_upwards [log_mean_upper_uniform hS heps] with n hn
  intro k hk
  apply (Real.log_le_iff_le_exp (meanAbsolute_all_shift_pos n k)).mp
  have hh := (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mp (hn k hk)
  simpa only [mul_comm] using hh

end
end SlowEquilibration.GOEWholeLinePotential
