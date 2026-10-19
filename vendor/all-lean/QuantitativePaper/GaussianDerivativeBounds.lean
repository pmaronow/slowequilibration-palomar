module
public import QuantitativePaper.SmoothGaussianPartition
public import QuantitativePaper.LogJetBounds

@[expose] public section

/-! Higher Gaussian log-partition derivatives with genuine bounds independent
of the evaluation point. These finite constants are used for posterior C⁴. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianDerivativePowerBound (m K : ℝ) (N : ℕ) : ℝ :=
  max 1 (∑ j ∈ Finset.range (N+1),|gaussianJetCoefficient m K j|)

theorem gaussianDerivativePowerBound_ge_one (m K : ℝ) (N : ℕ) :
    1 ≤ gaussianDerivativePowerBound m K N := le_max_left _ _

theorem gaussianJetCoefficient_le_power (m K : ℝ) (N j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ N) :
    gaussianJetCoefficient m K j ≤ (gaussianDerivativePowerBound m K N)^j := by
  have hh : |gaussianJetCoefficient m K j| ≤
      ∑ i ∈ Finset.range (N+1),|gaussianJetCoefficient m K i| :=
    Finset.single_le_sum (f := fun i => |gaussianJetCoefficient m K i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  exact (le_abs_self _).trans (hh.trans ((le_max_right _ _).trans
    (le_self_pow₀ (gaussianDerivativePowerBound_ge_one m K N) (by omega))))

theorem norm_iteratedFDeriv_log_gaussianShiftPartition_le {n : ℕ} (N j : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (A : Field n →L[ℝ] E) (m : ℝ) (hj0 : 1 ≤ j) (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Real.log (gaussianShiftPartition A m f y)) x‖ ≤
      (j.factorial : ℝ)*logJetCoefficient j*(gaussianDerivativePowerBound m K N)^j := by
  apply norm_iteratedFDeriv_log_le_of_relative (gaussianShiftPartition A m f)
    (contDiff_gaussianShiftPartition N f hf L hlip K hK hjets A m)
    (gaussianShiftPartition_pos f L hlip A m) hj0 hj _ x
  intro i hi hij
  exact (norm_iteratedFDeriv_gaussianShiftPartition_le N i f hf L hlip K hK hjets A m
    (hij.trans hj) x).trans (mul_le_mul_of_nonneg_right
      (gaussianJetCoefficient_le_power m K N i hi (hij.trans hj))
      (gaussianShiftPartition_pos f L hlip A m x).le)

end QuantitativePaper
