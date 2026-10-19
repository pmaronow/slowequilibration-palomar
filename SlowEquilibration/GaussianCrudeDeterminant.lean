-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianMatrixMomentLaw
public import SlowEquilibration.GaussianAffineDeterminantFinite

/-! Dimension-uniform crude determinant estimates from genuine Gaussian
spectral comparison and sharp top-eigenvalue concentration. The operator norm
is bounded by both actual edges; Frobenius mean growth is never substituted. -/

@[expose] public section
namespace SlowEquilibration.GaussianCrudeDeterminant

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge GaussianSpectralNorm
open GaussianAffineDeterminant SymmetricGaussianRealization SymmetricGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma upper_edge_exp_integrable
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j,W z i j=W z j i) {σ : ℝ} (hσ : 0 < σ) (hW : ‖W‖ ≤ σ) (r : ℝ) :
    Integrable (fun z => Real.exp (r*upperEigenvalue W z))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hG := upperEigenvalue_centered_subGaussian W hSym hσ hW
  let a := ∫ z,upperEigenvalue W z ∂SYK.standardGaussianMeasureOnEuclidean ι
  apply ((hG.integrable_exp_mul r).mul_const (Real.exp (r*a))).congr
  exact ae_of_all _ fun z => by
    change Real.exp (r*(upperEigenvalue W z-a))*Real.exp (r*a)=Real.exp (r*upperEigenvalue W z)
    rw [← Real.exp_add]
    congr 1
    dsimp only [a]
    ring

lemma upper_edge_exp_mean
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j,W z i j=W z j i) {σ : ℝ} (hσ : 0 < σ) (hW : ‖W‖ ≤ σ)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ z,Real.exp (r*upperEigenvalue W z) ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ 
      Real.exp (r*((Real.sqrt 2*σ)*Real.sqrt (n+1 : ℝ))+σ^2*r^2/2) := by
  have hG := upperEigenvalue_centered_subGaussian W hSym hσ hW
  let a := ∫ z,upperEigenvalue W z ∂SYK.standardGaussianMeasureOnEuclidean ι
  have hm := mean_upperEigenvalue_le W hSym hσ.le hW
  have hmgf := hG.mgf_le r
  simp only [mgf,Real.coe_toNNReal _ (sq_nonneg σ)] at hmgf
  have hf : (fun z => Real.exp (r*upperEigenvalue W z))=
      fun z => Real.exp (r*a)*Real.exp (r*(upperEigenvalue W z-a)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf,integral_const_mul]
  calc
    _ ≤ Real.exp (r*a)*Real.exp (σ^2*r^2/2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _=Real.exp (r*a+σ^2*r^2/2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left hm hr
      dsimp only [a]
      linarith)

lemma norm_exp_le_edges (A : GOEAsymptotics.GaussianMatrix (n+1)) (hA : ∀ i j,A i j=A j i)
    {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (r*‖gaussianMatrixCLM A‖) ≤ 
      Real.exp (r*matrixOrderedEigenvalues A 0)+Real.exp (r*matrixOrderedEigenvalues (-A) 0) := by
  let u := matrixOrderedEigenvalues A 0
  let v := matrixOrderedEigenvalues (-A) 0
  have huv : 0 ≤ max u v := by
    have h := neg_eigenvalue_le_upper A hA 0
    have hu : u ≤ max u v := le_max_left _ _
    have hv : v ≤ max u v := le_max_right _ _
    dsimp only [u,v] at hu hv ⊢
    linarith
  have hn := operator_norm_le_edges A hA huv (le_max_left _ _) (le_max_right _ _)
  calc
    _ ≤ Real.exp (r*max u v) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hr)
    _ ≤ _ := by
      rcases le_total u v with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (Real.exp_pos _).le

lemma rawDet_le_norm_exp (A : GOEAsymptotics.GaussianMatrix (n+1)) (hA : ∀ i j,A i j=A j i) (k : ℝ) :
    GaussianMatrixMomentLaw.rawDet 0 k A ≤ Real.exp ((n+1 : ℝ)*(|k|+‖gaussianMatrixCLM A‖)) := by
  unfold GaussianMatrixMomentLaw.rawDet
  rw [zero_add,GOEClippedDeterminants.shifted_det_eq_prod k A hA,Finset.abs_prod]
  have hi (i : Fin (n+1)) : |k-matrixOrderedEigenvalues A i| ≤ 
      Real.exp (|k|+‖gaussianMatrixCLM A‖) := by
    calc
      _ ≤ |k|+|matrixOrderedEigenvalues A i| := abs_sub _ _
      _ ≤ |k|+‖gaussianMatrixCLM A‖ := by linarith [eigenvalue_abs_le_operator_norm A hA i]
      _ ≤ _ := by linarith [Real.add_one_le_exp (|k|+‖gaussianMatrixCLM A‖)]
  have hp : (∏ i : Fin (n+1),|k-matrixOrderedEigenvalues A i|) ≤ 
      ∏ _i : Fin (n+1),Real.exp (|k|+‖gaussianMatrixCLM A‖) :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hi i)
  apply hp.trans_eq
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul,
    Nat.cast_add,Nat.cast_one]

/-- Crude constant uniform in all source dimensions and all real shifts. -/
def crudeConstant (b : ℝ) : ℝ := Real.log 2+2*Real.sqrt b+b

/-- Actual linear Gaussian matrix, all m=n+1 ≤ N and all real k. -/
theorem realization_crude_mean {N : ℕ}
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j,W z i j=W z j i) (hN : n+1 ≤ N)
    {b : ℝ} (hb : 0 < b) (hW : ‖W‖ ≤ Real.sqrt (2*b/N)) (k : ℝ) :
    Integrable (fun z => GaussianMatrixMomentLaw.rawDet 0 k (W z))
      (SYK.standardGaussianMeasureOnEuclidean ι) ∧
    (∫ z,GaussianMatrixMomentLaw.rawDet 0 k (W z) ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ 
      Real.exp ((N:ℝ)*(crudeConstant b+|k|)) := by
  have hNp : 0 < N := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hNp
  let σ := Real.sqrt (2*b/N)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hneg : ∀ z i j,(-W) z i j=(-W) z j i := by
    intro z i j
    change -W z i j=-W z j i
    rw [hSym]
  have hWneg : ‖-W‖ ≤ σ := by simpa only [norm_neg] using hW
  let r : ℝ := n+1
  have hr : 0 ≤ r := by positivity
  let F := fun z => Real.exp (r*upperEigenvalue W z)
  let G := fun z => Real.exp (r*upperEigenvalue (-W) z)
  have hF := upper_edge_exp_integrable W hSym hσ hW r
  have hG := upper_edge_exp_integrable (-W) hneg hσ hWneg r
  have hdom (z) : GaussianMatrixMomentLaw.rawDet 0 k (W z) ≤ Real.exp (r*|k|)*(F z+G z) := by
    apply (rawDet_le_norm_exp (W z) (hSym z) k).trans
    rw [mul_add,Real.exp_add]
    exact mul_le_mul_of_nonneg_left (norm_exp_le_edges (W z) (hSym z) hr) (Real.exp_pos _).le
  have hIntMajor : Integrable (fun z => Real.exp (r*|k|)*(F z+G z))
      (SYK.standardGaussianMeasureOnEuclidean ι) := (hF.add hG).const_mul _
  have hInt : Integrable (fun z => GaussianMatrixMomentLaw.rawDet 0 k (W z))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    apply hIntMajor.mono' ((GaussianMatrixMomentLaw.rawDet_measurable 0 k).comp W.continuous.measurable).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖GaussianMatrixMomentLaw.rawDet 0 k (W z)‖≤Real.exp (r*|k|)*(F z+G z)
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ GaussianMatrixMomentLaw.rawDet 0 k (W z) from abs_nonneg _)]
      exact hdom z
  refine ⟨hInt,?_⟩
  have hEF := upper_edge_exp_mean W hSym hσ hW hr
  have hEG := upper_edge_exp_mean (-W) hneg hσ hWneg hr
  have hmN : (n+1 : ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hedge : ((Real.sqrt 2*σ)*Real.sqrt (n+1 : ℝ)) ≤ 2*Real.sqrt b := by
    rw [edge_scale_eq hb.le]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
    apply (div_le_iff₀ hNr).mpr
    exact mul_le_mul_of_nonneg_left hmN hb.le
  have hexp : r*((Real.sqrt 2*σ)*Real.sqrt (n+1 : ℝ))+σ^2*r^2/2 ≤ 
      (N:ℝ)*(2*Real.sqrt b+b) := by
    have hs : σ^2=2*b/(N:ℝ) := Real.sq_sqrt (by positivity)
    rw [hs]
    have hrN : r ≤ (N:ℝ) := hmN
    have he := mul_le_mul_of_nonneg_left hedge hr
    have he2 := mul_le_mul_of_nonneg_right hrN (by positivity : 0 ≤ 2*Real.sqrt b)
    have hp : r^2 ≤ (N:ℝ)^2 := pow_le_pow_left₀ hr hrN 2
    have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ b/(N:ℝ))
    have ht' : (2*b/(N:ℝ))*r^2/2 ≤ (N:ℝ)*b := by
      convert ht using 1 <;> field_simp
    nlinarith
  have hFinal : r*|k|+Real.log 2+(N:ℝ)*(2*Real.sqrt b+b) ≤ 
      (N:ℝ)*(crudeConstant b+|k|) := by
    have hk := mul_le_mul_of_nonneg_right hmN (abs_nonneg k)
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hNp
    have hl := mul_le_mul_of_nonneg_right hN1 hlog
    unfold crudeConstant
    nlinarith
  calc
    _ ≤ ∫ z,Real.exp (r*|k|)*(F z+G z) ∂SYK.standardGaussianMeasureOnEuclidean ι := integral_mono hInt hIntMajor hdom
    _=Real.exp (r*|k|)*((∫ z,F z ∂SYK.standardGaussianMeasureOnEuclidean ι)+
      ∫ z,G z ∂SYK.standardGaussianMeasureOnEuclidean ι) := by rw [integral_const_mul,integral_add hF hG]
    _ ≤ Real.exp (r*|k|)*(2*Real.exp ((N:ℝ)*(2*Real.sqrt b+b))) := by
      gcongr
      have hf := hEF.trans (Real.exp_le_exp.mpr hexp)
      have hg := hEG.trans (Real.exp_le_exp.mpr hexp)
      linarith
    _=Real.exp (r*|k|+Real.log 2+(N:ℝ)*(2*Real.sqrt b+b)) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hFinal

/-- Law-level version for every centered symmetric Gaussian with the literal
manuscript covariance domination, including singular covariance. -/
theorem gaussian_crude_mean {N : ℕ}
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ]
    (hmean : ∫ A,A ∂μ=0) (hSym : ∀ᵐ A ∂μ,∀ i j,A i j=A j i)
    (hN : n+1 ≤ N) {b : ℝ} (hb : 0 < b)
    (hvar : ∀ M : GOEAsymptotics.GaussianMatrix (n+1),(∀ i j,M i j=M j i) →
      Var[fun A => Matrix.trace (entries A*entries M);μ] ≤ 
        (2*b/N)*Matrix.trace (entries M*entries M)) (k : ℝ) :
    Integrable (GaussianMatrixMomentLaw.rawDet 0 k) μ ∧
    (∫ A,GaussianMatrixMomentLaw.rawDet 0 k A ∂μ) ≤ Real.exp ((N:ℝ)*(crudeConstant b+|k|)) := by
  obtain ⟨W,hW,hWs,hμ⟩ := exists_realization_of_trace_variance μ hmean hSym hb.le hvar
  have ht := realization_crude_mean W hWs hN hb hW k
  rw [← hμ]
  constructor
  · exact (integrable_map_measure (GaussianMatrixMomentLaw.rawDet_measurable 0 k).aestronglyMeasurable
      W.continuous.measurable.aemeasurable).mpr ht.1
  · rw [integral_map W.continuous.measurable.aemeasurable
      (GaussianMatrixMomentLaw.rawDet_measurable 0 k).aestronglyMeasurable]
    exact ht.2

end
end SlowEquilibration.GaussianCrudeDeterminant
